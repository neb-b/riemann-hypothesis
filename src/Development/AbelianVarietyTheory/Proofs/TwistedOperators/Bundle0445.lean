module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearGKMapExtendsToSmoothVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedMatrixGroupOfLocalMultiplier
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatPoint

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem ev_apply (v : HeightOneSpectrum (𝓞 F)) (x : Af F) : evalV F v x = x v := rfl

theorem val_coe_one (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    Valued.v (algebraMap F (Af F) (t : F) v) = 1 := by
  rw [GlobalTheory.Ker.MovLev.val_coe]; exact v.intValuation_eq_one_iff.2 ht

theorem coe_ne_zero (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    algebraMap F (Af F) (t : F) v ≠ 0 := fun h0 => by
  have := val_coe_one t v ht
  rw [h0, map_zero] at this
  exact zero_ne_one this

theorem div_int {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F)
    (t : 𝓞 F) (ht : t ∉ v.asIdeal) : x * (algebraMap F (Af F) (t : F) v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [map_mul, map_inv₀, val_coe_one t v ht, inv_one, mul_one]
  exact hx

def mulG (I : Ideal (𝓞 F)) : AddSubgroup (Af F) :=
  AddSubgroup.closure {x | ∃ t ∈ I, ∃ β ∈ intAf F, x = algebraMap F (Af F) (t : F) * β}

theorem mem_mulG (I : Ideal (𝓞 F)) {γ : Af F} (hγ : γ ∈ intAf F)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), evalV F w γ = 0 ∨ ∃ t ∈ I, t ∉ w.asIdeal) : γ ∈ mulG I := by
  by_cases h0 : γ = 0
  · rw [h0]; exact zero_mem _
  obtain ⟨w₀, hw₀⟩ : ∃ w, γ w ≠ 0 := by
    by_contra H
    push_neg at H
    exact h0 (FiniteAdeleRing.ext F fun v => H v)
  obtain ⟨t₁, ht₁I, ht₁w⟩ := (h w₀).resolve_left hw₀
  have ht₁0 : t₁ ≠ 0 := fun e => ht₁w (e ▸ w₀.asIdeal.zero_mem)
  have hspan : Ideal.span {t₁} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht₁0
  set Z := (Ideal.finite_factors hspan).toFinset with hZdef
  have hZ : ∀ v, v ∈ Z ↔ t₁ ∈ v.asIdeal := fun v => by
    rw [hZdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t ∈ I, γ v = 0 ∨ t ∉ v.asIdeal := fun v =>
    (h v).elim (fun e => ⟨0, I.zero_mem, Or.inl e⟩) fun ⟨t, ht, hv⟩ => ⟨t, ht, Or.inr hv⟩
  choose τ hτI hτ using h'
  obtain ⟨c, hc, hc'⟩ : ∃ c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ∀ v, algebraMap F (Af F) (τ v : F) v * c v = γ v := by
    refine ⟨fun v => if γ v = 0 then 0 else γ v * (algebraMap F (Af F) (τ v : F) v)⁻¹, fun v => ?_, fun v => ?_⟩
    · dsimp only
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ ((hτ v).resolve_left hv)
    · dsimp only
      split_ifs with hv
      · rw [mul_zero, hv]
      · rw [mul_comm, mul_assoc, inv_mul_cancel₀ (coe_ne_zero _ _ ((hτ v).resolve_left hv)), mul_one]
  have hb₁ : ∀ v : HeightOneSpectrum (𝓞 F),
      (if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹) ∈ v.adicCompletionIntegers F :=
    fun v => by
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ hv
  obtain ⟨β₁, hβ₁, eβ₁⟩ : ∃ β₁ : Af F, β₁ ∈ intAf F ∧
      ∀ v, β₁ v = if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹ :=
    ⟨GlobalTheory.Ker.MovLev.ofInt _ hb₁, fun v => hb₁ v, fun _ => rfl⟩
  have hbw : ∀ w v : HeightOneSpectrum (𝓞 F), (if v = w then c v else 0) ∈ v.adicCompletionIntegers F :=
    fun w v => by
      split_ifs
      exacts [hc v, zero_mem _]
  have hβex : ∀ w : HeightOneSpectrum (𝓞 F), ∃ β : Af F, β ∈ intAf F ∧ ∀ v, β v = if v = w then c v else 0 :=
    fun w => ⟨GlobalTheory.Ker.MovLev.ofInt _ (hbw w), fun v => hbw w v, fun _ => rfl⟩
  choose β hβ eβ using hβex
  have e : γ = algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w := by
    refine FiniteAdeleRing.ext F fun v => ?_
    change evalV F v γ = evalV F v (algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, map_mul]
    simp only [map_mul, ev_apply, eβ₁, eβ]
    by_cases hv : t₁ ∈ v.asIdeal
    · have hvZ : v ∈ Z := (hZ v).2 hv
      rw [Finset.sum_eq_single v (fun w _ hwv => by rw [if_neg (Ne.symm hwv), mul_zero])
        (fun hn => absurd hvZ hn), if_pos hv, if_pos rfl, mul_zero, zero_add, hc']
    · rw [Finset.sum_eq_zero (fun w hw => by
        have hne : v ≠ w := fun e => hv (e ▸ (hZ w).1 hw)
        rw [if_neg hne, mul_zero]), if_neg hv, add_zero, mul_comm, mul_assoc,
        inv_mul_cancel₀ (coe_ne_zero _ _ hv), mul_one]
  rw [e]
  refine add_mem (AddSubgroup.subset_closure ⟨t₁, ht₁I, β₁, hβ₁, rfl⟩) (sum_mem fun w _ => ?_)
  exact AddSubgroup.subset_closure ⟨τ w, hτI w, β w, hβ w, rfl⟩

theorem pairA_mul_tmul {E : Type} [Field E] [Algebra F E] (s : F) (β : Af F) (x : E) :
    pairA F 0 (algebraMap F (Af F) s * β) ⊗ₜ[F] x = pairA F 0 β ⊗ₜ[F] (algebraMap F E s * x) := by
  have h : pairA F 0 (algebraMap F (Af F) s * β) = s • pairA F 0 β :=
    Prod.ext (by change (0 : Ainf F) = s • 0; rw [smul_zero]) (by change _ = s • β; rw [Algebra.smul_def]; rfl)
  rw [h, TensorProduct.smul_tmul, Algebra.smul_def]

end Gen

theorem mem_hatA_of_div : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  intro D S T A hA γ hγ y hy
  let I : Ideal (𝓞 D.host.F) :=
    { carrier := {t | algebraMap D.host.F D.host.E (t : D.host.F) • y ∈ A}
      add_mem' := fun {a b} ha hb => by
        change algebraMap D.host.F D.host.E ((a : D.host.F) + (b : D.host.F)) • y ∈ A
        rw [map_add (f := _), add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change algebraMap D.host.F D.host.E (0 : D.host.F) • y ∈ A
        rw [map_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c {x} hx => by
        change algebraMap D.host.F D.host.E ((c : D.host.F) * (x : D.host.F)) • y ∈ A
        rw [map_mul, mul_smul]
        exact hA c _ hx }
  have hmem := mem_mulG I hγ fun w => (hy w).imp id fun ⟨t, ht, hA'⟩ => ⟨t, hA', ht⟩
  let f : Af D.host.F →+ WO S T :=
    { toFun := fun α => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a
      map_zero' := Matrix.ext fun a k => by
        change pairA D.host.F 0 0 ⊗ₜ[D.host.F] y k a = 0
        exact TensorProduct.zero_tmul _ _
      map_add' := fun α β => Matrix.ext fun a k => by
        change pairA D.host.F 0 (α + β) ⊗ₜ[D.host.F] y k a =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a + pairA D.host.F 0 β ⊗ₜ[D.host.F] y k a
        rw [← TensorProduct.add_tmul]
        congr 1
        exact Prod.ext (add_zero 0).symm rfl }
  have hle : mulG I ≤ (hatA S T A).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, β, hβ, rfl⟩
    refine AddSubgroup.subset_closure ⟨β, hβ, _, ht, ?_⟩
    refine Matrix.ext fun a k => ?_
    change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (t : D.host.F) * β) ⊗ₜ[D.host.F] y k a =
      pairA D.host.F 0 β ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) • y) k a
    rw [pairA_mul_tmul, Matrix.smul_apply, smul_eq_mul]
  exact hle hmem

end GlobalTheory.HatPoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

variable {D : D7}

def kerPD (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A₁ : Fr W₁) (B : Fr X)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) :
    Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :=
  Submodule.span ℂ {Φ₀D | Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
    ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0}

theorem mem_kerPD {ψ : AddChar (AF D.host.F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (θ : InfFam D) {W W₁ X : HSp D}
    (A₁ : Fr W₁) (B : Fr X) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) (Φ₀D : (Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :
    Φ₀D ∈ kerPD ψ θ A₁ B Bs Γ cB p' ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
      ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  have hl := isDatum_linear Γ.M' ψ hψ (⇑cB)
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, hl.1, map_zero p'⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    obtain ⟨hy1, Φy, hΦy, hDy, hpy⟩ := hy
    refine ⟨Submodule.add_mem _ hx1 hy1, Φx + Φy, Submodule.add_mem _ hΦx hΦy, ?_, by rw [map_add (f := _), hpx, hpy, add_zero]⟩
    have := hl.2 x y Φx Φy 1 hDx hDy
    simpa using this
  | smul c x _ hx =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    refine ⟨Submodule.smul_mem _ c hx1, c • Φx, Submodule.smul_mem _ c hΦx, ?_, by rw [map_smul, hpx, smul_zero]⟩
    have := hl.2 0 x 0 Φx c hl.1 hDx
    simpa using this

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearCuspFormFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section

namespace GlobalTheory.GKGlobalise

theorem kFin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) = GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
  apply le_antisymm
  · refine sSup_le fun W hW v hv => ?_
    exact ⟨W, hW.1, hv, hW.2⟩
  · rintro v ⟨A, hA, hv, hs⟩
    exact le_sSup (show A ∈ {W : Submodule ℂ (M.H τ) | FiniteDimensional ℂ W ∧
      Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W} from ⟨hA, hs⟩) hv

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := fun v hv =>
  (_root_.GlobalTheory.SmVecModel.mem_sm_iff M τ v).2 ((GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)).2.2.1 v hv)

end GlobalTheory.GKGlobalise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ArrowLiftAut

theorem isQuot_of_is {D : D7} {N : GlobalTheory.Grid.Node D} (m : N.MeasDat) (df : Prop)
    (K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))) (h : m.Is df K) :
    GlobalTheory.Mem.Th.IsQuot N.V m.ν m.fd := by
  by_cases hd : df
  · obtain ⟨⟨hH, -⟩, hF⟩ := h.1 hd
    exact And.intro hH hF
  · obtain ⟨⟨hH, -⟩, hF⟩ := h.2 hd
    exact And.intro hH hF

theorem isQuot_cast {D : D7} {S S' : GlobalTheory.Grid.Node D} (e : S = S') (m : S.MeasDat)
    (h : GlobalTheory.Mem.Th.IsQuot S.V m.ν m.fd) :
    GlobalTheory.Mem.Th.IsQuot S'.V (m.cast e).ν (m.cast e).fd := by
  subst e
  exact h

theorem lift_isAutFunSm (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {θ : InfFam D} (hθ : IsInfFam θ)
    {ψ : AddChar (AF ↥D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep S T}
    (hω : IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (GlobalTheory.Grid.WRep.toSgn true ω))
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hq : GlobalTheory.Mem.Th.IsQuot T ν 𝓕)
    {Φ : WO (GlobalTheory.Grid.sgn true S) T → ℂ} (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn true S) T Φ)
    {φ : GA D T → ℂ} (hφ : IsAutFunSm θ T φ) (hφc : IsCuspFun T φ) :
    IsAutFunSm θ S (fun h => ∫ g in 𝓕, thetaKO ω h g Φ * φ g ∂ν) := by
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  have hK := (GlobalTheory.Mem.Lift.isKerSys_thKer hθ hω.std hW hω.om_cont).swap
  have hL := (GlobalTheory.Mem.Lift.IsKerSys.lift hCRD hθ hK hq ⟨hφ, hφc⟩ ⟨Φ, hΦ⟩).2
  exact ((GlobalTheory.sgn_fun_cusp D θ hθ true S (fun h => ∫ g in 𝓕, thetaKO ω h g Φ * φ g ∂ν)).1).1 hL

private theorem isQuot_Yc_nuY_fdY_of_base {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R) (t : T) (k : ℕ) (hk : k < D.R.m) :
    GlobalTheory.Mem.Th.IsQuot (Yc D k) (R.νY t k) (R.fdY t k) := by
  rcases Nat.lt_or_ge (k + 1) D.R.m with h | h
  · obtain ⟨⟨hH, -⟩, hF⟩ := hR.measY t k h
    exact And.intro hH hF
  · obtain rfl : k = D.R.m - 1 := by omega
    obtain ⟨⟨hH, -⟩, hF⟩ := hR.measY' t
    exact And.intro hH hF

theorem isQuot_meas {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R) (hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R) (hG : G.Is)
    (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j ≤ D.R.m) :
    GlobalTheory.Mem.Th.IsQuot (G.V i j).V (G.meas t i j).ν (G.meas t i j).fd := by
  have hM := hG.meas
  rcases i with _ | i
  · rcases j with _ | j
    · exact isQuot_of_is _ _ _ (hM.col 0 (Nat.zero_le _))
    · dsimp only [GlobalTheory.Grid.GridPre.meas, GlobalTheory.Grid.meas0]
      split_ifs with h1
      · exact isQuot_cast _ _ (isQuot_Yc_nuY_fdY_of_base R hR t (j + 1) h1)
      · refine isQuot_cast _ _ ?_
        obtain ⟨⟨hH, -⟩, hF⟩ := hR.measX t
        exact And.intro hH hF
  · rcases j with _ | j
    · exact isQuot_of_is _ _ _ (hM.col (i + 1) hi.le)
    · exact isQuot_of_is _ _ _ (hM.vert i j hi.le hj)

end GlobalTheory.ArrowLiftAut

namespace GlobalTheory.ArrowLiftAut

end GlobalTheory.ArrowLiftAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqUnitaryEmbeddingOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

theorem norm_sq_unitaryEmbedding_add : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (x : GA D Y) (τ : D.what₂.Tau) (y : Fin Y.rank → D.host.E) (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) ^ 2 = nrm θ A x τ y ^ 2 + ‖tauE D τ u‖ ^ 2 := by
  intro D θ hθ Y V d A B hAd x τ y u
  let φ : AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ :=
    (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hinc : ∀ e, φ (incA D e) = tauE D τ e := by
    intro e
    have := (hθ τ).1 e
    simpa [φ, incA, inclR] using this
  have hcmp : ∀ {W : HSp D} (g : GA D W), cmp θ τ g = (matHom W g).1.map φ := by
    intro W g; rfl
  have hinv : (stabilizerEmbedding d x)⁻¹ = stabilizerEmbedding d x⁻¹ :=
    (map_inv (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)) x).symm
  set P := (frameMat V Y d.ι).map (tauE D τ) with hP
  set Q := (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) with hQ
  have key : cmp θ τ (stabilizerEmbedding d x)⁻¹ = GlobalTheory.UnitaryEmbeddingProperties.ex P Q (cmp θ τ x⁻¹) := by
    rw [hinv, hcmp, hcmp, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, GlobalTheory.UnitaryEmbeddingProperties.ex_map, Matrix.map_map, Matrix.map_map]
    have hf : (⇑φ ∘ ⇑(incA D)) = ⇑(tauE D τ) := funext hinc
    rw [hf]
  have hQP : Q * P = 1 := GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map (tauE D τ) d
  have hQz0 : GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ zv d = 0 := by
    have hp := d.perp
    have h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V Y d.ι) * V.gram) *ᵥ zv d = 0 := by
      funext i
      have := congr_fun (congr_fun hp i) 0
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, zv] using this
    rw [GlobalTheory.UnitaryEmbeddingProperties.qM, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hQz : Q *ᵥ (fun i => tauE D τ (zv d i)) = 0 := by
    funext i
    have := congr_fun hQz0 i
    rw [hQ]
    change ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) *ᵥ (⇑(tauE D τ) ∘ zv d)) i = 0
    rw [← RingHom.map_mulVec, this]
    exact map_zero _
  have hvec : (fun i => tauE D τ ((frameMat V Y d.ι *ᵥ y + u • zv d) i)) =
      P *ᵥ (fun i => tauE D τ (y i)) + tauE D τ u • fun i => tauE D τ (zv d i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hP, RingHom.map_mulVec]
    rfl
  have hex : ∀ (h : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (w : Fin Y.rank → ℂ) (a : ℂ),
      GlobalTheory.UnitaryEmbeddingProperties.ex P Q h *ᵥ (P *ᵥ w + a • fun i => tauE D τ (zv d i)) =
        P *ᵥ (h *ᵥ w) + a • fun i => tauE D τ (zv d i) := by
    intro h w a
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, GlobalTheory.UnitaryEmbeddingProperties.ex_mul_P P Q hQP,
      ← Matrix.mulVec_mulVec]
    congr 2
    rw [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hQz,
      Matrix.mulVec_zero, add_zero]
  unfold nrm
  rw [key, hvec, hex]
  exact hAd τ _ _

end GlobalTheory.SepPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

abbrev Arr (D : D7) : Type := Fin D.R.m ⊕ Fin D.R.m

def arrP (t : T) : Arr D → Pair T
  | .inl j => .top t j
  | .inr i => .chi i D.R.m


variable (G) in
abbrev Vecs (t : T) : Type := ∀ a : Arr D, WO (G.pS (arrP t a)) (G.pT (arrP t a)) → ℂ

def vecsOf (S : GridChoice W U) {t : T} (d : PureDat G t) : Vecs G t
  | .inl j => S.Z.vec (d.1 j)
  | .inr i => S.Z.vec (d.2 i)

def kkVec (S : GridChoice W U) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  S.Z.scal 1 p • fockComp W S.N.frC p f (x * S.N.u _) (y * S.N.u _)

def colV (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowV (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairVec (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (fs : Vecs G t) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂ (colV S fs x) (rowV S fs y)

theorem pairPts_eq (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) (v w) :
    pairPts S τ x y v w = τ.sum fun d a => a * pairVec S x y (vecsOf S d) v w := by
  unfold pairPts Finsupp.sum
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

def first : Arr D := .inl ⟨0, by have := D.R.two_le_m; omega⟩

def moveFirst (W : G.Weil) {t : T} (g : FinPt G (.top 0)) (fs : Vecs G t) : Vecs G t :=
  Function.update fs first (W.om (.top t 0) (G.toPair (.top t 0) g.1 1) (fs first))

end GlobalTheory.TopZeroInv
end
end

