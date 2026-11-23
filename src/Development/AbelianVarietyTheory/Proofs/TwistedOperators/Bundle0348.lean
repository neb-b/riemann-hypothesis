module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicConditionLastTorusDiagonalIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
noncomputable section

namespace GlobalTheory.AscFin.IsoDiag


set_option maxHeartbeats 1000000 in
theorem last_diag_int_iso : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ ξ ∈ p.B₁, ∀ ξ' : Mx D ρ V₀.rank, MxAt (· = v) ξ → mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ ξ' → ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ')) = ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ))) → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ hstd V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast t ht htG hiso i hi
  obtain ⟨eV, heV_int, heV_act, heV_cA, -⟩ := GlobalTheory.FinPl.LastDiag.exists_idemAt D v
  have heV_id : eV ∈ idAt D (· = v) := heV_int.1
  have hcA : ∀ c ∈ idAt D (· = v), cA D c ∈ idAt D (· = v) := fun c hc => by
    rw [← heV_act c hc, map_mul, heV_cA]; exact Ideal.mul_mem_left _ _ heV_id
  have hMx : ∀ c ∈ idAt D (· = v), MxAt (· = v) (dW.incAdj V₀ (c • yZero V₀ ρ z)) :=
    fun c hc k l => by
      rw [GlobalTheory.FinPl.LastDiag.incAdj_smul, Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (hcA c hc)
  have hcong := (GlobalTheory.IwaPlace.mem_congGrp_iff W (idAt D (· = v)) _).1 htG
  have hM : MxAt (· = v) (mt W (dW.levi t) - 1) := fun k l => by rw [Matrix.sub_apply]; exact hcong k l
  have htM : t.1 - 1 = dW.pX ⬝ (mt W (dW.levi t) - 1) ⬝ dW.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, dW.pX_levi t, Matrix.mul_one, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have ha : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := GlobalTheory.FinPl.LastDiag.mxAt_mul_right (GlobalTheory.FinPl.LastDiag.mxAt_mul_left dW.pX hM) dW.jX i i
    rwa [← htM, Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hρ : 0 < ρ := by omega
  rw [← hlast hρ _ ha]
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hstd V₀ W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ ha)).2 fun u' hu' => ?_
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = dW.pX ⬝ u' := ⟨_, rfl⟩
  have hξ : MxAt (· = v) ξ := hξdef ▸ GlobalTheory.FinPl.LastDiag.mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu')
  have hu : dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) :=
    hξdef ▸ GlobalTheory.FinPl.LastDiag.wittExtZero_inclusionX_mem_homLatticeCompletion dV dW hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hu'
  have hB : ξ ∈ p.B₁ := (hS.b ξ hξ).2 hu
  have hact : mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ (t.1 ⬝ ξ) := by
    rw [HypDec.incX_apply, HypDec.incX_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, HypDec.levi_jX]
  have hχ := hiso ξ hB (t.1 ⬝ ξ) hξ hact
  rw [GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc,
    GlobalTheory.FinPl.LastDiag.yZero_mul_diag _ _ t.1 ht i hi, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj] at hχ
  rw [GlobalTheory.FinPl.LastDiag.symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sub_mul, one_mul,
    map_sub, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, hχ, ← AddChar.map_add_eq_mul]
  rw [add_neg_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.AscFin.IsoDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeepsLatticeAtPlaceOfIntegralLocalBasisConjugate
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.KeepInt

theorem mulVec_conj_mem {d : ℕ} {K : Type} [Field K] (S : ValuationSubring K)
    (b : GL (Fin d) K) (M : Matrix (Fin d) (Fin d) K) (w : Fin d → K)
    (hM : ∀ i j, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M * (b : Matrix (Fin d) (Fin d) K)) i j ∈ S)
    (hw : ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) i ∈ S) :
    ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (M *ᵥ w)) i ∈ S := by
  intro i
  have key : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (M *ᵥ w) =
      (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M * (b : Matrix (Fin d) (Fin d) K)) *ᵥ
        (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) := by
    have h1 : (b : Matrix (Fin d) (Fin d) K) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (b : Matrix (Fin d) (Fin d) K), h1, Matrix.mul_one]
  rw [key]
  simp only [Matrix.mulVec, dotProduct]
  exact S.sum_mem (fun j _ => mul_mem (hM i j) (hw j))

end GlobalTheory.KeepInt

theorem GlobalTheory.KeepInt.keepLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) →
  ∀ A : Matrix (Fin d) (Fin d) (AE F E), (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) → (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  intro F E _ _ _ _ _ d W v π₁ π₂ b₁ b₂ hiff A hA₁ hA₂ z hz
  obtain ⟨hAt, h₁, h₂⟩ := (hiff z).1 hz
  refine (hiff _).2 ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [← Matrix.mulVec_smul, hAt u hu, Matrix.mulVec_zero]
  · have e : (fun j => π₁ ((A *ᵥ z) j)) = (A.map π₁) *ᵥ (fun j => π₁ (z j)) := by
      funext j; exact RingHom.map_mulVec π₁ A z j
    rw [e]
    exact GlobalTheory.KeepInt.mulVec_conj_mem (v.adicCompletionIntegers F) b₁ _ _ hA₁ h₁
  · have e : (fun j => π₂ ((A *ᵥ z) j)) = (A.map π₂) *ᵥ (fun j => π₂ (z j)) := by
      funext j; exact RingHom.map_mulVec π₂ A z j
    rw [e]
    exact GlobalTheory.KeepInt.mulVec_conj_mem (v.adicCompletionIntegers F) b₂ _ _ hA₂ h₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizerAtPlaceMemDepthCongruenceGridNo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.LevelOffS

variable {D : D7}

theorem valued_algebraMap {v : GlobalTheory.FinPl.Pl D} (y : D.host.F) :
    Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) y) = v.valuation D.host.F y :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y

theorem inv_int {v : GlobalTheory.FinPl.Pl D} {c : 𝓞 D.host.F} (hc : c ∉ v.asIdeal) :
    evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (algebraMap (𝓞 D.host.F) D.host.F c)⁻¹) ∈
      v.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.intValuation c = 1 := le_antisymm (v.intValuation_le_one c)
    (not_lt.1 fun h => hc ((v.intValuation_lt_one_iff_mem c).1 h))
  have h2 : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (algebraMap (𝓞 D.host.F) D.host.F c)) = 1 := by
    rw [valued_algebraMap]
    exact (HeightOneSpectrum.valuation_of_algebraMap v c).trans h1
  rw [map_inv₀, map_inv₀, h2, inv_one]

theorem coe_ne_zero_of_nmem {v : GlobalTheory.FinPl.Pl D} {c : 𝓞 D.host.F} (hc : c ∉ v.asIdeal) :
    algebraMap (𝓞 D.host.F) D.host.F c ≠ 0 := by
  intro h
  apply hc
  rw [show c = 0 from IsFractionRing.injective (𝓞 D.host.F) D.host.F (h.trans (map_zero _).symm)]
  exact zero_mem _

theorem smul_pairA (r : D.host.F) (α : Af D.host.F) : r • pairA D.host.F 0 α = pairA D.host.F 0 (r • α) :=
  Prod.ext (smul_zero (A := Ainf D.host.F) r) rfl

theorem smul_vec_apply (c : 𝓞 D.host.F) {n : ℕ} (x : Fin n → D.host.E) (i : Fin n) :
    (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • x) i = algebraMap (𝓞 D.host.F) D.host.F c • x i := by
  rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
  congr 1

theorem latV_le_smul {S : HSp D} (Λ : Lat S) {v : GlobalTheory.FinPl.Pl D} (𝔪 : Ideal (𝓞 D.host.E)) {c : 𝓞 D.host.F}
    (hc : c ∉ v.asIdeal) (hcm : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ 𝔪) :
    latV S Λ (· = v) ≤ latV S (𝔪 • Λ) (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  rw [AddSubgroup.closure_le]
  rintro _ ⟨α, hα, hαv, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  set cF : D.host.F := algebraMap (𝓞 D.host.F) D.host.F c with hcF
  have hc0 : cF ≠ 0 := coe_ne_zero_of_nmem hc
  refine AddSubgroup.subset_closure ⟨α * algebraMap D.host.F (Af D.host.F) cF⁻¹, fun w => ?_, fun w hw => ?_, 1, rfl,
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • x, Submodule.smul_mem_smul hcm hx, ?_⟩
  · rw [map_mul]
    by_cases hw : w = v
    · subst hw
      exact mul_mem (hα w) (inv_int hc)
    · rw [hαv w hw, zero_mul]
      exact zero_mem _
  · rw [map_mul, hαv w hw, zero_mul]
  · funext i
    rw [smul_vec_apply, one_mul, one_mul, ← TensorProduct.smul_tmul, smul_pairA]
    congr 2
    rw [Algebra.smul_def, mul_left_comm, ← map_mul, mul_inv_cancel₀ hc0, map_one, mul_one]

theorem finPart_finIn (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (GlobalTheory.FinPlLoc.finIn D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [GlobalTheory.FinPlLoc.finIn_tmul, GlobalTheory.FinPlLoc.finPart_pair]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem finIn_mem_idAt (z : Af D.host.F ⊗[D.host.F] D.host.E) : GlobalTheory.FinPlLoc.finIn D z ∈ idAt D (fun _ => True) := by
  unfold GlobalTheory.FinPl.idAt
  exact Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (GlobalTheory.FinPlLoc.infPart_finIn z),
    (Submodule.mem_iInf _).2 fun w => absurd trivial w.2⟩

theorem hatL_mono {n : ℕ} {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ ≤ Λ') :
    Formalism.L2.Herm.hatL (F := D.host.F) Λ ≤ Formalism.L2.Herm.hatL (F := D.host.F) Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_GfC_of_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {κ : GA D S} (h : κ ∈ grpAt S P) : κ ∈ GfC S := by
  unfold GlobalTheory.FinPl.grpAt at h
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at h
  show infHom S κ = 1
  apply Units.ext
  ext i j
  have h1 := GlobalTheory.FinPlLoc.infPart_of_idAt (h i j)
  rw [map_sub, sub_eq_zero] at h1
  change infPart D (mt S κ i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j
  rw [h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem finE_coe {S : HSp D} (κ : GA D S) :
    ((Lev.finE S κ : GL (Fin S.rank) (Lev.EAf D)) : Matrix (Fin S.rank) (Fin S.rank) (Lev.EAf D)) =
      (mt S κ).map ((Lev.swapAE D).comp (finPart D)) := rfl

theorem sub_mem_hatL_of_inK {S : HSp D} (Λ : Lat S) {v : GlobalTheory.FinPl.Pl D} (𝔪 : Ideal (𝓞 D.host.E)) {c : 𝓞 D.host.F}
    (hc : c ∉ v.asIdeal) (hcm : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ 𝔪) {κ : GA D S}
    (hκ : InK S Λ (· = v) κ) (x : Fin S.rank → Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    ((Lev.finE S κ : GL (Fin S.rank) (Lev.EAf D)) : Matrix (Fin S.rank) (Fin S.rank) (Lev.EAf D)) *ᵥ x - x ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) := by
  obtain ⟨z, hz⟩ : ∃ z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E, ∀ i, Lev.swapAE D (z i) = x i :=
    ⟨fun i => (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (x i), fun i => by
      show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
        ((Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (x i)) = x i
      generalize x i = y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]⟩
  set y0 : Fin S.rank → AE D := fun i => GlobalTheory.FinPlLoc.finIn D (z i) with hy0def
  have hφ : ∀ i, (Lev.swapAE D).comp (finPart D) (y0 i) = x i := fun i => by
    rw [RingHom.comp_apply, hy0def, finPart_finIn, hz]
  have hy0 : y0 ∈ latV S Λ (fun _ => True) := by
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D S Λ _ y0 (fun i => finIn_mem_idAt _) ?_
    convert hx using 1
    funext i
    exact hφ i
  set e := GlobalTheory.FinPlLoc.idem D (· = v) with he
  have hey : e • y0 ∈ latV S Λ (· = v) := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt _) hy0
  have hmv : mt S κ *ᵥ (e • y0) ∈ latV S Λ (· = v) := (hκ.2 _ (GlobalTheory.FinPlLoc.latV_idAt hey)).1 hey
  have hgrp := hκ.1
  unfold GlobalTheory.FinPl.grpAt at hgrp
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at hgrp
  have hN : ∀ i j, e * (mt S κ - 1) i j = (mt S κ - 1) i j := fun i j =>
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (by rw [Matrix.sub_apply]; exact hgrp i j)
  have hd : mt S κ *ᵥ (e • y0) - e • y0 = mt S κ *ᵥ y0 - y0 := by
    have h1 : ∀ w : Fin S.rank → AE D, mt S κ *ᵥ w - w = (mt S κ - 1) *ᵥ w := fun w => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [h1, h1, Matrix.mulVec_smul]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hN i j]
  have hd' : mt S κ *ᵥ y0 - y0 ∈ latV S (𝔪 • Λ) (· = v) :=
    latV_le_smul Λ 𝔪 hc hcm (hd ▸ sub_mem hmv hey)
  have hfin := GlobalTheory.LatVHat.latV_mem_hatL D S (𝔪 • Λ) _ _ hd'
  convert hfin using 1
  funext i
  have hx' : x = ⇑((Lev.swapAE D).comp (finPart D)) ∘ y0 := funext fun j => (hφ j).symm
  rw [finE_coe, Pi.sub_apply, Pi.sub_apply, hx', ← RingHom.map_mulVec]
  change _ = (Lev.swapAE D).comp (finPart D) ((mt S κ *ᵥ y0 - y0) i)
  rw [Pi.sub_apply, map_sub]
  rfl

theorem exists_unit_mem_modul {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ G.pl.S0) : ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.modul := by
  classical
  have hex : ∀ u ∈ G.pl.S0, ∃ c ∈ u.asIdeal, c ∉ v.asIdeal := by
    intro u hu
    by_contra h
    push_neg at h
    have huv : u = v := HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top h)
    exact hv (huv ▸ hu)
  choose! f hf hfv using hex
  refine ⟨∏ u ∈ G.pl.S0, f u ^ G.pl.depth sc u, fun hmem => ?_, ?_⟩
  · obtain ⟨u, hu, hu'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact hfv u hu (v.isPrime.mem_of_pow_mem _ hu')
  · show _ ∈ ∏ u ∈ G.pl.S0, (G.pl.w u).asIdeal ^ G.pl.depth sc u
    rw [map_prod]
    apply Ideal.prod_mem_prod
    intro u hu
    rw [map_pow]
    apply Ideal.pow_mem_pow
    have h1 := G.pl.under_w hu
    have h2 : f u ∈ ((G.pl.w u).under (𝓞 D.host.F)).asIdeal := by rw [h1]; exact hf u hu
    exact h2

end GlobalTheory.LevelOffS


open GlobalTheory.LevelOffS in
theorem GlobalTheory.LevelOffS.inK_mem_lev : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → ∀ v, v ∉ G.pl.S0 → ∀ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ → κ ∈ lev G (.grid i 0) := by
  intro D hD T L μ0 hL sc G W M hM i hi v hv κ hκ
  obtain ⟨c, hc, hcm⟩ := exists_unit_mem_modul G hv
  refine Subgroup.mem_inf.2 ⟨mem_GfC_of_grpAt hκ.1, ?_⟩
  rw [Subgroup.mem_comap]
  show _ ∈ GlobalTheory.ChiGrid.congLev D.sp.cm (G.V (.grid i 0)).gram (G.Λ (.grid i 0)) G.modul
  rw [GlobalTheory.ChiGrid.mem_congLev]
  have hle : Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.grid i 0)) ≤ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid i 0)) :=
    hatL_mono Submodule.smul_le_right
  refine ⟨GlobalTheory.DefFree.finE_mem _ κ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩,
    fun x hx => sub_mem_hatL_of_inK _ _ hc hcm hκ x hx⟩
  · have h1 := hle (sub_mem_hatL_of_inK _ _ hc hcm hκ x hx)
    have h2 := add_mem h1 hx
    rwa [sub_add_cancel] at h2
  · have h1 := hle (sub_mem_hatL_of_inK _ _ hc hcm (inK_inv hκ) _ hx)
    have h2 := add_mem h1 hx
    rw [sub_add_cancel, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h2
    exact h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineHomTransportLatticeVacua
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapVac

variable {D : D7}

theorem lnk_simil {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') :
    l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L.gram := by
  rw [Int.cast_one, one_mul]
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  exact mul_right_cancel₀ b c

theorem lnk_tau_ne {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') : l.τ ≠ 0 := by
  intro h0
  have e := l.map
  rw [h0, Matrix.zero_mulVec] at e
  have hz : ζ = 0 := neg_eq_zero.mp e.symm
  have n : D.host.xi0 * star D.host.xi0 * (star ζ' ⬝ᵥ L.gram *ᵥ ζ') = 0 := by
    rw [← l.norm, hz]; simp
  rcases mul_eq_zero.1 n with h1 | h1
  · rcases mul_eq_zero.1 h1 with h3 | h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D (star_eq_zero.1 h3)
  · exact h.2 h1

theorem kap_surj {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) :
    Function.Surjective (l.κ S) := by
  obtain ⟨σ, _, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  intro x
  refine ⟨(rat σ : Mx D L.rank L.rank) ⬝ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S x, ?_⟩
  rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

theorem kap_add {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : l.κ S (v + w) = l.κ S v + l.κ S w :=
  (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).1 v w

theorem kap_sympl {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : symplOH L S (l.κ S v) (l.κ S w) = -symplOH S L v w := by
  have e := (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).2.2.2.2.1 v w
  unfold symplOH
  rw [e, Int.cast_one, one_mul, mul_neg]

theorem kap_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E}
    (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) (Ξ : WO L S → ℂ) (w' : WO S L)
    (hw : heisO ψ S L w' (fun w => star (Ξ (l.κ S w))) = fun w => star (Ξ (l.κ S w))) :
    heisO ψ L S (l.κ S w') Ξ = Ξ := by
  funext x
  obtain ⟨v, rfl⟩ := kap_surj h l S x
  have e := congrFun hw v
  simp only [heisO] at e
  have e2 := congrArg (starRingEnd ℂ) e
  rw [map_mul, GlobalTheory.AdjLawPf.conj_psi ψ hψ] at e2
  simp only [starRingEnd_apply, star_star] at e2
  simp only [heisO]
  rw [kap_sympl h l, ← kap_add h l]
  exact e2

theorem half_mul_left {m n k : ℕ} {e : AE D} (M : Mx D m n) {x : Mx D n k} (hx : IsHalf e x) : IsHalf e (M ⬝ x) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx]

theorem half_mul_right {m n k : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (M : Mx D n k) : IsHalf e (x ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hx]

theorem half_smul {m n : ℕ} {e : AE D} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx]

theorem half_adj {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) := by
  intro i j
  show cA D e * cA D (x j i) = cA D (x j i)
  rw [← map_mul, hx]

theorem split_conj {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := he
  exact ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hv,
    by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]⟩

theorem kap_half {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    {e : AE D} {w : WO S L} (hh : IsHalf e (l.κ S w)) : IsHalf (cA D e) w := by
  obtain ⟨σ, hστ, _⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  have h1 : IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S (l.κ S w)) :=
    half_smul _ (half_mul_left _ (half_mul_right (half_adj hh) _))
  rw [Lnk.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj] at h1
  have h2 := half_mul_left (rat σ : Mx D L.rank L.rank) h1
  rwa [← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul] at h2

theorem kappa_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → ∀ (L S : HSp D) (ζ ζ' : Fin L.rank → D.host.E), IsLineVec L ζ' → ∀ (l : Lnk L ζ L ζ') (Λ : AddSubgroup (WO S L)) (Ξ : WO L S → ℂ), IsLatVac (heisO ψ S L) Λ (fun w => star (Ξ (l.κ S w))) → ∀ w ∈ Λ, heisO ψ L S (2 • l.κ S w) Ξ = Ξ ∧ ∀ e, IsSplitIdem D e → IsHalf e (l.κ S w) → heisO ψ L S (l.κ S w) Ξ = Ξ := by
  intro D ψ hψ L S ζ ζ' h l Λ Ξ hv w hw
  refine ⟨?_, fun e he hh => ?_⟩
  · have e2 : (2 • l.κ S w : WO L S) = l.κ S (2 • w) := by rw [two_nsmul, two_nsmul, kap_add h l]
    rw [e2]
    exact kap_heis ψ hψ h l S Ξ _ (hv.1 w hw)
  · exact kap_heis ψ hψ h l S Ξ w (hv.2 (cA D e) (split_conj he) w hw (kap_half h l S hh))

end GlobalTheory.KapVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.CharXFB
variable {D : D7}

def hA (T : HSp D) (y z : Fin T.rank → AE D) : AE D := ∑ k, cA D (z k) * (gA T *ᵥ y) k

theorem pairS_eq_sum (T : HSp D) {ρ : ℕ} (x x' : Mx D T.rank ρ) :
    pairS T x x' = ∑ p, hA T (fun k => x k p) (fun k => x' k p) := by
  simp only [pairS, hA, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem mxAt_of_mem_depLat {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {p : Pair T}
    {u : WO (G.pS p) (G.pT p)} (hu : u ∈ depLat G p) : MxAt (fun _ => True) u :=
  GlobalTheory.FinPl.LatMem.latO_mxAt hu.1

end GlobalTheory.CharXFB
end
end

