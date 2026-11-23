module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0063
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonconstantRationalCurveNonproperGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
public import GroundTheory.GlobalFields.CompletionAtPlace.Galois
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import GroundTheory.GlobalFields.CompletionAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrModelOfIsLin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.BigNZ

open GlobalTheory.WeilM GlobalTheory.AdelicU

section Generic

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {Y : Spc F E d}

def IsFinPart (M : Model σ X Y) (T : Finset (Pl F)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) ∧ ∀ v, v ∉ T → φ v = M.vac v

def IsLagrModel (M : Model σ X Y) (ψ : AddChar (AF F) ℂ) (v : Pl F) (A A' : Set (Matrix (Fin n) (Fin d) (AE F E)))
    {Z : Type} [TopologicalSpace Z] [Add Z] (co : Matrix (Fin n) (Fin d) (AE F E) → Z)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Z → ℂ)) : Prop :=
  Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB Z : Set _) ∧
  (∀ u ∈ A, ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ z, ι φ₁ z = ι φ (z + co u)) ∧
  ∀ u ∈ A', ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ x ∈ A,
    ι φ₁ (co x) = ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) x u) * ι φ (co x)

theorem isFinPart_vac {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} (h : M.IsGood ψ) (T : Finset (Pl F)) : IsFinPart M T M.vac :=
  ⟨fun v => (h.vac v).1, fun _ _ => rfl⟩

theorem isLagrModel_of_isLin {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : Pl F} {π₁ π₀ : AE F E →+* Fv F v} {co ι}
    (h : M.IsLin ψ π₁ π₀ co ι) :
    IsLagrModel M ψ v {u | At (evFin F v) u ∧ u.map π₀ = 0} {u | At (evFin F v) u ∧ u.map π₁ = 0} co ι :=
  ⟨h.bij, fun u hu => h.trans u hu.1 hu.2, fun u hu φ hφ φ₁ hφ₁ a x hx => h.mult u hu.1 hu.2 φ hφ φ₁ hφ₁ a x hx.1 hx.2⟩

end Generic

section Grid

open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num Geo IsTripleOf mulG colV adjV₁)
open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def IsTied (t : T) (i j : ℕ) (e : Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop :=
  Γ.V.L = conjSub (G.Λ (.grid (i + 1) (j + 1))) ∧
  Γ.W.L = pairLat (scLat D.host.AA (G.Λ (.grid i (j + 1)))) (conjSub (scLat D.host.AA (conjSub (G.Λ (.grid (i + 1) j))))) e ∧
  (∀ v, v ∈ X.T ↔ ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) ∧
  ∀ v : Bs.P, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v.1 → splitPrime (Bs.τ v) = w

variable {i j : ℕ}

def mixHalf (e : Num G i j) (ε : AE D) :
    Set (Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :=
  {u | IsHalf ε (mulG (negSp (spW G i j)) (colV e u)ᵀ) ∧ IsHalf ε (adjV₁ e u)}

def mixCo (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) :=
  fromCols (B.coord t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      ((mulG (negSp (spW G i j)) (colV e u)ᵀ).map fun a => cpt w (toEAf D a)))
    (B.coord t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ ((adjV₁ e u).map fun a => cpt w (toEAf D a)))ᵀ

def IsLocFn (W : G.Weil) (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (Γ : Geo G i j) (w : Pl D.host.E)
    (v : Pl D.host.F) (Ψ : Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ)
    (φ : (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ) : Prop :=
  φ ∈ SB _ ∧ ∃ ι, IsLagrModel Γ.M W.ψ v (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧ ι φ = Ψ

end Grid

end GlobalTheory.BigNZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_finprod_schwartzBruhat_finiteAdeles : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    IsLocallyConstant (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  first | exact @GlobalTheory.WeilM.isLocallyConstant_finprod_evalV | exact GlobalTheory.WeilM.isLocallyConstant_finprod_evalV | (intros; apply GlobalTheory.WeilM.isLocallyConstant_finprod_evalV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.HeisLatVac

theorem lc_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IsotropicVectorExistence.main
  | exact _root_.GlobalTheory.IsotropicVectorExistence.main
  | (apply _root_.GlobalTheory.IsotropicVectorExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsotropicVectorExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsotropicVectorExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsotropicVectorExistence.main ..)

theorem lc_exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀) : ∃ U₀ : OpenAddSubgroup K, ∀ t ∈ U₀, ψ₀ t = 1 := by
  have hV : {t : K | ‖ψ₀ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => lc_pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

theorem lc_val {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hy : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (u : (κ → K) × (κ → K)) (hu : u ∈ Λ) :
    vacFn ψ₀ Λ χ x₀ (x₀ + u.1) = χ u * ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
  have h : ∃ u' ∈ Λ, x₀ + u.1 = x₀ + u'.1 := ⟨u, hu, rfl⟩
  rw [vacFn, dite_eq_left h]
  obtain ⟨hw, hwe⟩ := h.choose_spec
  generalize h.choose = w at hw hwe ⊢
  have h1 : w.1 = u.1 := (add_left_cancel hwe).symm
  have hyΛ : ((0 : κ → K), w.2 - u.2) ∈ Λ := by
    have e : ((0 : κ → K), w.2 - u.2) = w - u := Prod.ext (by simp [h1]) rfl
    rw [e]; exact Λ.sub_mem hw hu
  have hwu : w = u + (0, w.2 - u.2) := Prod.ext (by simp [h1]) (by simp)
  have e2 : χ w = χ u * χ (0, w.2 - u.2) * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ (w.2 - u.2) - (0 : κ → K) ⬝ᵥ u.2)) := by
    conv_lhs => rw [hwu]
    exact hco u hu _ hyΛ
  rw [e2, hy _ hyΛ, h1, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [zero_dotProduct, sub_zero, dotProduct_sub]
  ring

theorem isLocallyConstant_vacFn {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] [TopologicalSpace K]
    [IsTopologicalRing K] [NonarchimedeanAddGroup K] (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (hΛ : IsOpen (Λ : Set ((κ → K) × (κ → K))))
    (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hy : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (h2 : ∀ u ∈ Λ, χ (u + u) = 1) : IsLocallyConstant (vacFn ψ₀ Λ χ x₀) := by
  obtain ⟨U₀, hU₀⟩ := lc_exists_open_ker ψ₀ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  by_cases hx : ∃ u ∈ Λ, x = x₀ + u.1
  · obtain ⟨u, hu, rfl⟩ := hx
    have hN : {s : κ → K | (⅟(2 : K) • s, (0 : κ → K)) ∈ Λ ∧ s ⬝ᵥ u.2 ∈ (U₀ : Set K)} ∈ nhds (0 : κ → K) := by
      refine IsOpen.mem_nhds ?_ ?_
      · refine (hΛ.preimage ?_).inter (U₀.isOpen.preimage ?_)
        · exact (continuous_id.const_smul (⅟(2 : K))).prodMk (continuous_const : Continuous fun _ : κ → K => (0 : κ → K))
        · exact continuous_id.dotProduct continuous_const
      · refine ⟨?_, ?_⟩
        · show (⅟(2 : K) • (0 : κ → K), (0 : κ → K)) ∈ Λ
          rw [smul_zero, Prod.mk_zero_zero]; exact Λ.zero_mem
        · show (0 : κ → K) ⬝ᵥ u.2 ∈ (U₀ : Set K)
          rw [zero_dotProduct]; exact U₀.zero_mem
    filter_upwards [hN] with s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hs0 : (s, (0 : κ → K)) ∈ Λ := by
      have e : (s, (0 : κ → K)) = (⅟(2 : K) • s, (0 : κ → K)) + (⅟(2 : K) • s, (0 : κ → K)) := by
        refine Prod.ext ?_ (by simp)
        simp only [Prod.fst_add]
        rw [← add_smul, invOf_two_add_invOf_two, one_smul]
      rw [e]; exact Λ.add_mem hs1 hs1
    have hχs : χ (s, 0) = 1 := by
      have e : (s, (0 : κ → K)) = (⅟(2 : K) • s, (0 : κ → K)) + (⅟(2 : K) • s, (0 : κ → K)) := by
        refine Prod.ext ?_ (by simp)
        simp only [Prod.fst_add]
        rw [← add_smul, invOf_two_add_invOf_two, one_smul]
      rw [e]; exact h2 _ hs1
    have hx' : x₀ + u.1 + s = x₀ + (u + (s, 0)).1 := by simp [add_assoc]
    have hneg : ψ₀ (-(s ⬝ᵥ u.2)) = 1 := hU₀ _ (U₀.neg_mem hs2)
    rw [hx', lc_val ψ₀ Λ χ x₀ hco hy _ (Λ.add_mem hu hs0), lc_val ψ₀ Λ χ x₀ hco hy u hu,
      hco u hu _ hs0, hχs, mul_one, mul_assoc, ← AddChar.map_add_eq_mul]
    have key : ⅟(2 : K) * (u.1 ⬝ᵥ (s, (0 : κ → K)).2 - (s, (0 : κ → K)).1 ⬝ᵥ u.2) +
        (-(x₀ ⬝ᵥ (u + (s, 0)).2) - ⅟(2 : K) * ((u + (s, 0)).1 ⬝ᵥ (u + (s, 0)).2)) =
        -(s ⬝ᵥ u.2) + (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
      simp only [Prod.fst_add, Prod.snd_add, add_zero, dotProduct_zero, add_dotProduct]
      linear_combination (-(s ⬝ᵥ u.2)) * (invOf_two_add_invOf_two : ⅟(2 : K) + ⅟(2 : K) = 1)
    rw [key, AddChar.map_add_eq_mul, hneg, one_mul]
  · have h0 : vacFn ψ₀ Λ χ x₀ x = 0 := by rw [vacFn, dite_eq_right hx]
    have hN : {s : κ → K | (s, (0 : κ → K)) ∈ Λ} ∈ nhds (0 : κ → K) := by
      refine IsOpen.mem_nhds (hΛ.preimage (continuous_id.prodMk (continuous_const : Continuous fun _ : κ → K => (0 : κ → K)))) ?_
      show ((0 : κ → K), (0 : κ → K)) ∈ Λ
      rw [Prod.mk_zero_zero]; exact Λ.zero_mem
    filter_upwards [hN] with s hs
    rw [h0, vacFn, dite_eq_right]
    rintro ⟨u, hu, e⟩
    refine hx ⟨u - (s, 0), Λ.sub_mem hu hs, ?_⟩
    simp only [Prod.fst_sub]
    rw [← add_sub_assoc, ← e, add_sub_cancel_right]

end GlobalTheory.HeisLatVac


open GlobalTheory.HeisLatVac in
theorem GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, χ (u + u) = 1) → IsLocallyConstant (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  intro F _ _ v κ _ ψ₀ hψ Λ hΛ χ x₀ hco hy h2
  exact isLocallyConstant_vacFn ψ₀ hψ Λ hΛ χ x₀ hco hy h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfManyTorsionPointsCharZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ManyTorsionProper

theorem isProper_of_many_torsion_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ _ G _ hG g hg m s hs hcard
  by_contra hnp
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hcard
    · exact h
  obtain ⟨P, hP, u, a, b, hu, hab⟩ := _root_.GlobalTheory.RatCurve.exists_rational_curve k G hG hnp
  obtain ⟨k', _, _, p, _, _, G', _, hG', hg', hm', ⟨s', hs', hc'⟩, P', hP', u', a', b', hu', hab'⟩ :=
    _root_.GlobalTheory.CharPSpec.exists_charP_specialization k G hG g hg m hm s hs P hP u a b hu hab
  have hpr : IsProper G'.hom :=
    _root_.GlobalTheory.SerreTateProperness.main k' p G' hG' g hg' m hm' s' hs' (by rw [hc']; exact hcard)
  exact hab' (_root_.GlobalTheory.NoRatCurve.maps_from_open_line_const k' G' (GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G' hG' hpr) P' hP' u' a' b' hu')

end GlobalTheory.ManyTorsionProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothCharCompNormU
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCChar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def normU (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] :
    (u.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  Units.map (Algebra.norm (v.adicCompletion K) : u.adicCompletion L →* v.adicCompletion K)

theorem isSmoothChar_comp_normU (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L))
    [u.asIdeal.LiesOver v.asIdeal] {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSmoothChar (χ.comp (normU v u)) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion L) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K L (u.adicCompletion L)]
  have hfd : FiniteDimensional (v.adicCompletion K) (u.adicCompletion L) := GroundTheory.Global.finite_adicCompletion v u
  have hc := (GlobalTheory.adicCompletion_trace_norm_continuous K L v u _ (GroundTheory.Global.continuous_adicCompletionMap v u) hfd).2
  unfold IsSmoothChar at hχ ⊢
  rw [← MonoidHom.comap_ker]
  exact hχ.preimage (Continuous.units_map _ hc)

end GlobalTheory.BCChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharFromIsStd

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (y : Af F) :
    ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  set t : ℝ := 1 / (2 * n)
  refine ⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩
  rw [psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have eR : (n • t : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    simp only [t]
    rw [mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]
    ring
  have e : ((n • t : ℝ) : ℂ) = 1 / 2 := by
    rw [eR]; push_cast; ring
  rw [e]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end GlobalTheory.StdCharFromIsStd

namespace GlobalTheory.StdCharFromIsStd

theorem isStdChar_of_isStd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsStdChar D ψ (-1) := by
  intro D ψ hψ
  refine ⟨isCharAF hψ, GlobalTheory.DualPairCompare.exists_infFam D, fun θ hθ x => ?_⟩
  change ψ (pairA D.host.F x 0) = _
  rw [psi_pairA hψ, GlobalTheory.DualPairCompare.sum_infFam θ hθ, GlobalTheory.BaseGoodPlace.trInf_eq_trace]
  congr 1
  push_cast
  ring

end GlobalTheory.StdCharFromIsStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentImagesOfRankOneLattice
section
open NumberField

namespace GlobalTheory

theorem linearIndependent_images_of_rankOne_lattice :
    ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := by
  intro K _ _ p m n ell M v hv 𝔟 h𝔟 hell hinj hind
  obtain ⟨β, hβ, hβ0⟩ := (Submodule.ne_bot_iff 𝔟).1 h𝔟
  refine hind.linearIndependent _ (fun a => ?_) (fun a => ?_)
  · have hmem : M a (β • v) ∈ Submodule.span K
        ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) :=
      Submodule.subset_span ⟨β • v, (hell _).2 ⟨β, hβ, rfl⟩, rfl⟩
    have : M a v = β⁻¹ • M a (β • v) := by
      rw [map_smul, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  · intro h
    exact hv ((hinj a) (by rw [h, map_zero]))

end GlobalTheory
end

