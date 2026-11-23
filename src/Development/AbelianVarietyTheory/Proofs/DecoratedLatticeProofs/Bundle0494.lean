module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterAdelicUnitaryGroupFinitePartScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseMovesVectorZ
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMemLineLatticeCompletionIffScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.KappaLeft

theorem latV_mem_idAt {D : D7} {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : ∀ r, y r ∈ idAt D P := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, s, -, rfl⟩ := hw
    intro r
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => intro r; exact zero_mem _
  | add x y _ _ hx hy => intro r; exact add_mem (hx r) (hy r)
  | neg x _ hx => intro r; exact neg_mem (hx r)

end GlobalTheory.Corev.KappaLeft


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Corev.kappa_mem_latO_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x : WO S B'.L, MxAt P x → ((B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ)) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ σ B B' l S α α₀ M LS Λ hM hLS hα x hx
  have hcA : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  have hMx : MxAt P ((B.o.resS S).symm (0, l.κ S x)) :=
    (GlobalTheory.KapLatSupp.mxAt_embed_kappa D ρ B B'.L B'.ζ l S B'.V₀ B'.A B'.o P x hx).1
  have hu : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]

  have hline : ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ v : Fin L.rank → AE D,
      (∀ r, v r ∈ idAt D P) → ∃ c : AE D, c ∈ idAt D P ∧ v = c • ratV ζ := by
    intro L ζ hL v hv
    obtain ⟨hrk, hne⟩ := hL
    have hr : ∀ r r' : Fin L.rank, r = r' := fun r r' => Fin.ext (by omega)
    let r₀ : Fin L.rank := ⟨0, by omega⟩
    have hζ : ζ r₀ ≠ 0 := by
      intro h0
      apply hne
      have : ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
      rw [this, Matrix.mulVec_zero, dotProduct_zero]
    refine ⟨v r₀ * incA D (ζ r₀)⁻¹, Ideal.mul_mem_right _ _ (hv r₀), ?_⟩
    funext r
    rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
  have hjB : ∀ c : AE D, B.o.jB *ᵥ (c • ratV B.ζ) = fun r => c * incA D (vecB B.o B.ζ r) := by
    intro c
    funext r
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
      map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpj : ∀ c : AE D, B.o.pB *ᵥ (B.o.jB *ᵥ (c • ratV B.ζ)) = c • ratV B.ζ := by
    intro c
    rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]

  have hsupp : ∀ m : Fin B.V₀.rank → AE D, ∀ r, (((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m) r ∈ idAt D P := by
    intro m r
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hMx r j)

  have hpair : ∀ (y : Fin S.rank → AE D) (d c : AE D), (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ →
      (∑ i, ∑ j, cA D (y i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ)) j) =
        incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) := by
    intro y d c hxy
    rw [_root_.GlobalTheory.kappa_adj D ρ B B'.L B'.ζ l S x (c • ratV B.ζ) y]
    have h1 : ((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ y = d • ratV (-B.ζ) := by
      rw [← Matrix.mulVec_mulVec, hxy, Matrix.mulVec_smul, ← l.map]
      congr 1
      ext i
      simp [rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [h1]
    have hh : incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) =
        ∑ i, ∑ j, incA D (star (B.ζ i)) * incA D (HSpace.gram B.L i j) * incA D (B.ζ j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Finset.mul_sum, mul_assoc]
    rw [hh, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ratV, Pi.neg_apply, map_mul, map_neg, hcA, star_neg]
    ring
  rw [_root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P, _root_.GlobalTheory.FinPl.UnitPlaces.latA_eq_latV D k ι p I P hP S LS]
  constructor
  · rintro ⟨-, h⟩ y hy
    have hz : ∀ r, ((x : Matrix _ _ (AE D)) *ᵥ y) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r j)
    obtain ⟨d, hdI, hxd⟩ := hline B'.L B'.ζ B'.line _ hz
    refine ⟨d, hdI, hxd, fun c hc hl => ?_⟩
    have hm : (fun r => c * incA D (vecB B.o B.ζ r)) ∈ latV B.V₀ M P :=
      (_root_.GlobalTheory.LineIdeal.mem_latV_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).2 hl
    have h1 := h _ hm
    have hI := hsupp (fun r => c * incA D (vecB B.o B.ζ r))
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ (fun r => c * incA D (vecB B.o B.ζ r)) =
        (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← hjB, ← Matrix.mulVec_mulVec, hpj]
    rw [heq] at h1 hI
    have h2 := (_root_.GlobalTheory.FinPl.SelfDualCompl.selfDual_latV D S LS hLS P _ hI).1 h1 y hy
    rwa [hpair y d c hxd] at h2
  · intro h
    refine ⟨hMx, fun m hm => ?_⟩
    have hv : ∀ r, (B.o.pB *ᵥ m) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (GlobalTheory.Corev.KappaLeft.latV_mem_idAt hm j)
    obtain ⟨c, hc, hcv⟩ := hline B.L B.ζ B.line _ hv
    have hjp := _root_.GlobalTheory.LineProj.lineProj_mem D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα m hm
    rw [hcv, hjB] at hjp
    have hl := (_root_.GlobalTheory.LineIdeal.mem_latV_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).1 hjp
    have hI := hsupp m
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m = (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← Matrix.mulVec_mulVec, hcv]
    rw [heq] at hI ⊢
    refine (_root_.GlobalTheory.FinPl.SelfDualCompl.selfDual_latV D S LS hLS P _ hI).2 fun s hs => ?_
    obtain ⟨d, -, hxd, hd⟩ := h s hs
    rw [hpair s d c hxd]
    exact hd c hc hl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastWittLineOfBesselJacobiLatticesGood
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

def SameAt (v : GlobalTheory.FinPl.Pl D) (𝔞 𝔟 : FI D) : Prop := ∀ s ∈ idAt D (· = v), s ∈ idV 𝔞 v ↔ s ∈ idV 𝔟 v

theorem mem_idAt_of_idV {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {v : GlobalTheory.FinPl.Pl D} {𝔞 : FI D}
    {s : AE D} (hs : s ∈ idV 𝔞 v) : s ∈ idAt D (· = v) := by
  have h3 := (_root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v).2.2.1 𝔞 1 one_ne_zero s
  rw [FractionalIdeal.spanSingleton_one, one_mul] at h3
  exact (h3.1 hs).2

theorem sameAt_div {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {v : GlobalTheory.FinPl.Pl D} {𝔞 𝔞' 𝔟 𝔟' : FI D}
    (ha : 𝔞 ≠ 0) (ha' : 𝔞' ≠ 0) (hb : 𝔟 ≠ 0) (hb' : 𝔟' ≠ 0) (h𝔞 : SameAt v 𝔞 𝔞') (h𝔟 : SameAt v 𝔟 𝔟') :
    SameAt v (𝔟 * 𝔞⁻¹) (𝔟' * 𝔞'⁻¹) := by
  intro s hs
  have h2 := (_root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v).2.1
  rw [← h2 _ _ ha hb s hs, ← h2 _ _ ha' hb' s hs]
  constructor
  · intro h a haV
    have haA := mem_idAt_of_idV hψ haV
    exact (h𝔟 _ (Ideal.mul_mem_left _ s haA)).1 (h a ((h𝔞 a haA).2 haV))
  · intro h a haV
    have haA := mem_idAt_of_idV hψ haV
    exact (h𝔟 _ (Ideal.mul_mem_left _ s haA)).2 (h a ((h𝔞 a haA).1 haV))

theorem sameAt_trans {v : GlobalTheory.FinPl.Pl D} {𝔞 𝔟 𝔠 : FI D} (h1 : SameAt v 𝔞 𝔟) (h2 : SameAt v 𝔟 𝔠) : SameAt v 𝔞 𝔠 :=
  fun s hs => (h1 s hs).trans (h2 s hs)

theorem sameAt_refl (v : GlobalTheory.FinPl.Pl D) (𝔞 : FI D) : SameAt v 𝔞 𝔞 := fun _ _ => Iff.rfl

theorem sameAt_mul_of_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {v : GlobalTheory.FinPl.Pl D} {𝔠 𝔫 : FI D}
    (hc : 𝔠 ≠ 0) (hn : 𝔫 ≠ 0) (h : SameAt v 1 𝔫) : SameAt v 𝔠 (𝔠 * 𝔫) := by
  have h1 : SameAt v (1 * 1⁻¹) (1 * 𝔫⁻¹) :=
    sameAt_div hψ one_ne_zero hn one_ne_zero one_ne_zero h (sameAt_refl v 1)
  have h2 := sameAt_div hψ (by simp) (by simpa using hn) hc hc h1 (sameAt_refl v 𝔠)
  simpa using h2

def col {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : Fin S.rank → D.host.E := fun k => d.e k i

theorem colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D) :
    colMul d.jX i a = a • ratV (col d i) := by
  funext k
  rfl

theorem col_ne_zero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : col d i ≠ 0 := by
  intro h
  have h' : ∀ k, d.e k i = 0 := fun k => congrFun h k
  have := congrFun (congrFun d.e'e i) i
  simp [Matrix.mul_apply, h'] at this

theorem vecB_ne_zero {S₀ A L : HSp D} (o : OrthDec S₀ A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) :
    vecB o ζ ≠ 0 := by
  intro h
  apply hζ.2
  rw [← o.isoB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have : o.iB *ᵥ ζ = 0 := h
  rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero]

end GlobalTheory.Core.Mi.ChainLast

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

theorem smul_colMul' {m n : ℕ} (x : Mx D m n) (i : Fin n) (s t : AE D) : s • colMul x i t = colMul x i (s * t) := by
  funext k
  simp only [colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem cols_sameAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {v : GlobalTheory.FinPl.Pl D}
    (hG : GoodBF ψ B J LV LV₀ LW LW₀ v) (i : Fin ρ) {𝔢 𝔟 : FI D} (h𝔟0 : 𝔟 ≠ 0)
    (h𝔢 : ∀ a ∈ idAt D (· = v), a • ratV (col B.d i) ∈ latV B.V LV (· = v) ↔ a ∈ idV 𝔢 v)
    (h𝔟 : ∀ a ∈ idAt D (· = v), a • ratV (col J.d i) ∈ latV J.W LW (· = v) ↔ a ∈ idV 𝔟 v) :
    SameAt v 𝔢 (𝔟 * (D.host.AA : FI D)) := by
  intro a ha
  obtain ⟨-, h2, -, -, -, -, h7⟩ := _root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hAA : (D.host.AA : FI D) ≠ 0 := GlobalTheory.CuspCharLattice.host_AA_ne_zero _
  rw [← h𝔢 a ha, ← colMul_jX, hG.cols i a ha, h7]
  have e : 𝔟 * (D.host.AA : FI D) = 𝔟 * ((D.host.AA : FI D)⁻¹)⁻¹ := by rw [inv_inv]
  rw [e, ← h2 _ _ (inv_ne_zero hAA) h𝔟0 a ha]
  constructor
  · rintro ⟨-, h⟩ t ht
    have htA := mem_idAt_of_idV hψ ht
    have h' := h t ht
    rw [smul_colMul', show xZero J.d = J.d.jX from rfl, colMul_jX, h𝔟 _ (Ideal.mul_mem_left _ t ha)] at h'
    rw [mul_comm]; exact h'
  · intro h
    refine ⟨fun k => Ideal.mul_mem_right _ _ ha, fun t ht => ?_⟩
    have htA := mem_idAt_of_idV hψ ht
    rw [smul_colMul', show xZero J.d = J.d.jX from rfl, colMul_jX, h𝔟 _ (Ideal.mul_mem_left _ t ha), mul_comm]
    exact h t ht

end GlobalTheory.Core.Mi.ChainLast

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}


open GlobalTheory.SeeSaw.LastPrim in
set_option maxHeartbeats 1000000 in
theorem last_sameAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {v : GlobalTheory.FinPl.Pl D}
    (hG : GoodBF ψ B J LV LV₀ LW LW₀ v) (i : Fin ρ) (hi : i.1 + 1 = ρ) {𝔷 : FI D} {𝔟 : ℕ → FI D}
    (h𝔷0 : 𝔷 ≠ 0) (h𝔷 : GlobalTheory.SeeSaw.LineId B.o B.ζ LV₀ 𝔷 v) (h𝔟0 : 𝔟 i ≠ 0) (hmono : GlobalTheory.SeeSaw.MonoId J.d LW LW₀ 𝔟 v) :
    SameAt v 1 (FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) * 𝔷) := by
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := _root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v
  obtain ⟨n, hn⟩ := i
  simp only at hi
  obtain rfl : n = ρ - 1 := by omega
  set i : Fin ρ := ⟨ρ - 1, hn⟩ with hi_def
  have hρ : 0 < ρ := by omega
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero
  have hAAb : (D.host.AAbar : FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hL := colMul_jY_mem_latA_iff D ψ hψ J.W J.W₀ ρ J.d LW (𝔟 i) v i h𝔟0
    (_root_.GlobalTheory.DualLine.dualLine_mem_iff D ψ hψ J.W J.W₀ ρ J.d LW LW₀ 𝔟 v hG.sdW hmono i h𝔟0)
  set 𝔑 : FI D := FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) with h𝔑
  have h𝔑0 : 𝔑 ≠ 0 := mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hξ)
    (mul_ne_zero hAAb (inv_ne_zero h𝔟0))
  have e : (D.host.AAbar : FI D) * (𝔟 i)⁻¹ = FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔑 := by
    rw [h𝔑, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
      FractionalIdeal.spanSingleton_one, one_mul]
  have e3 : incA D (D.host.xi0⁻¹)⁻¹ * incA D (star D.host.xi0⁻¹) = -1 := by
    rw [← map_mul, inv_inv, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, mul_neg, mul_inv_cancel₀ hξ, map_neg, map_one]
  have key : ∀ a ∈ idAt D (· = v), ∀ y ∈ latV B.V₀ LV₀ (· = v),
      (Matrix.mulVec (show Matrix (Fin J.W.rank) (Fin B.V₀.rank) (AE D) from
        J.d.incAdj B.V₀ (a • yZero B.V₀ ρ (vecB B.o B.ζ))) y ∈ GlobalTheory.FinPl.latA J.W LW (· = v) ↔
        a * cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l) ∈ idV 𝔑 v) := by
    intro a ha y hy
    have hzi : (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l) ∈ idAt D (· = v) :=
      sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem' hy l)
    rw [incAdj_yZero_mulVec D ρ B J hρ a y, hL _ (Ideal.mul_mem_left _ _ hzi), map_mul, map_mul, cA_cA,
      GlobalTheory.DualPairCheck.cA_incA, e, h3 _ _ (inv_ne_zero hξ)]
    have e4 : incA D (D.host.xi0⁻¹)⁻¹ * (incA D (star D.host.xi0⁻¹) * a *
        cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l)) =
        -(a * cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l)) := by
      rw [← mul_assoc, ← mul_assoc, e3]; ring
    rw [e4, neg_mem_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)⟩⟩
  intro a ha
  have e5 : 𝔑 * 𝔷 = 𝔑 * 𝔷⁻¹⁻¹ := by rw [inv_inv]
  rw [h1, ← hG.last hρ a ha, GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW, e5,
    ← h2 _ _ (inv_ne_zero h𝔷0) h𝔑0 a ha]
  constructor
  · rintro ⟨-, hu⟩ g hg
    obtain ⟨y, hy, hyg⟩ := _root_.GlobalTheory.SeeSaw.HzOnto.hz_onto D ψ hψ B.V₀ B.A B.L B.o B.ζ LV₀ 𝔷 v hG.sdV₀ h𝔷 h𝔷0 g hg
    rw [← hyg]
    exact (key a ha y hy).1 (hu y hy)
  · intro h
    have hcA : cA D a ∈ idAt D (· = v) := cA_mem_idAt'' ha
    refine ⟨fun k l => ?_, fun y hy => (key a ha y hy).2 (h _ (_root_.GlobalTheory.LineDual.line_pair_mem_idV D ψ hψ B.V₀ B.A B.L B.o B.ζ LV₀ 𝔷 v hG.sdV₀ h𝔷 h𝔷0 y hy))⟩
    have e6 := congrFun (incAdj_yZero_mulVec D ρ B J hρ a (Pi.single l 1)) k
    rw [Matrix.mulVec_single_one] at e6
    refine (congrArg (· ∈ idAt D (· = v)) e6).mpr ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcA))

end GlobalTheory.Core.Mi.ChainLast

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

theorem ideal_eq (𝔟 𝔷 : FI D) (h𝔟0 : 𝔟 ≠ 0) (h𝔷0 : 𝔷 ≠ 0) :
    𝔟 * (D.host.AA : FI D) * 𝔷⁻¹ *
      (FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * 𝔟⁻¹) * 𝔷) = GlobalTheory.SeeSaw.dI D := by
  calc 𝔟 * (D.host.AA : FI D) * 𝔷⁻¹ *
        (FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * 𝔟⁻¹) * 𝔷)
      = FractionalIdeal.spanSingleton _ D.host.xi0 * (D.host.AA : FI D) * (D.host.AAbar : FI D) * (𝔟 * 𝔟⁻¹) *
          (𝔷 * 𝔷⁻¹) := by ring
    _ = GlobalTheory.SeeSaw.dI D := by rw [mul_inv_cancel₀ h𝔟0, mul_inv_cancel₀ h𝔷0, mul_one, mul_one]; rfl

end GlobalTheory.Core.Mi.ChainLast


open GlobalTheory.Core.Mi.ChainLast in
theorem GlobalTheory.Core.Mi.LatMatch.lastAt_of_goodBF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : GlobalTheory.FinPl.Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → LastAt ψ B.d (vecB B.o B.ζ) LV LV₀ v := by
  intro D ψ hψ ρ B J LV LV₀ LW LW₀ v hG i hi s hs
  obtain ⟨-, h2, -, -, h5, -, -⟩ := _root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v
  obtain ⟨𝔢, h𝔢0, -, h𝔢⟩ := _root_.GlobalTheory.Core.Mi.LatLine.line_trace D B.V LV (col B.d i) hG.sdV (col_ne_zero _ _)
  obtain ⟨𝔷, h𝔷0, -, h𝔷⟩ := _root_.GlobalTheory.Core.Mi.LatLine.line_trace D B.V₀ LV₀ (vecB B.o B.ζ) hG.sdV₀ (vecB_ne_zero B.o B.line)
  let 𝔟 : ℕ → FI D := fun n => if h : n < ρ then
    Classical.choose (_root_.GlobalTheory.Core.Mi.LatLine.line_trace D J.W LW (col J.d ⟨n, h⟩) hG.sdW (col_ne_zero _ _)) else 1
  have h𝔟 : ∀ j : Fin ρ, 𝔟 j ≠ 0 ∧
      ∀ a ∈ idAt D (· = v), a • ratV (col J.d j) ∈ latV J.W LW (· = v) ↔ a ∈ idV (𝔟 j) v := by
    intro j
    have hs := Classical.choose_spec (_root_.GlobalTheory.Core.Mi.LatLine.line_trace D J.W LW (col J.d j) hG.sdW (col_ne_zero _ _))
    simp only [𝔟, dif_pos j.2, Fin.eta]
    exact ⟨hs.1, hs.2.2 v⟩
  have hmono : GlobalTheory.SeeSaw.MonoId J.d LW LW₀ 𝔟 v :=
    ⟨hG.monoW, fun j a ha => by rw [colMul_jX]; exact (h𝔟 j).2 a ha⟩
  have hA := cols_sameAt hψ hG i (h𝔟 i).1 (h𝔢 v) (h𝔟 i).2
  have hB := last_sameAt hψ hG i hi h𝔷0 (h𝔷 v) (h𝔟 i).1 hmono
  have hAA : (D.host.AA : FI D) ≠ 0 := GlobalTheory.CuspCharLattice.host_AA_ne_zero _
  have hAAb : (D.host.AAbar : FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero
  have hb0 : 𝔟 i * (D.host.AA : FI D) ≠ 0 := mul_ne_zero (h𝔟 i).1 hAA
  have hN0 : FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) * 𝔷 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hξ)
      (mul_ne_zero hAAb (inv_ne_zero (h𝔟 i).1))) h𝔷0
  have hC := sameAt_div hψ h𝔷0 h𝔷0 h𝔢0 hb0 (sameAt_refl v 𝔷) hA
  have hD := sameAt_mul_of_one hψ (mul_ne_zero hb0 (inv_ne_zero h𝔷0)) hN0 hB
  rw [ideal_eq (𝔟 i) 𝔷 (h𝔟 i).1 h𝔷0] at hD
  rw [← h5 s hs, ← sameAt_trans hC hD s hs, ← h2 𝔷 𝔢 h𝔷0 h𝔢0 s hs]
  constructor
  · intro h a haV
    have haA := mem_idAt_of_idV hψ haV
    have h' := h a haA ((h𝔷 v a haA).2 haV)
    rwa [colMul_jX, h𝔢 v _ (Ideal.mul_mem_left _ s haA)] at h'
  · intro h a haA haz
    rw [colMul_jX, h𝔢 v _ (Ideal.mul_mem_left _ s haA)]
    exact h a ((h𝔷 v a haA).1 haz)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairIdentity
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop

theorem lattice_ratio_vector_of_scalar_factorisation {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (e c θ θ' : R)
    (X X' Sm Sm' Kk Z : GL n R) (hZ : Z.val = c • (1 : Matrix n n R))
    (hT : X⁻¹ * Sm = Z * (X'⁻¹ * Sm') * Kk) (zY zY' Γ : n → R)
    (hm : e • Matrix.mulVec (Sm⁻¹).val zY = e • (θ • Γ)) (hm' : e • Matrix.mulVec (Sm'⁻¹).val zY' = e • (θ' • Γ)) :
    e • ((θ * c) • Matrix.mulVec ((X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹).val (Matrix.mulVec (X'⁻¹).val zY')) =
      e • (θ' • Matrix.mulVec (X⁻¹).val zY) := by
  set M := (X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹ with hM
  have hg : Z * M * X'⁻¹ = (X⁻¹ * Sm) * Sm'⁻¹ := by
    rw [hM, hT]; group
  have h2 : c • Matrix.mulVec M.val (Matrix.mulVec (X'⁻¹).val zY') = Matrix.mulVec (Z * M * X'⁻¹).val zY' := by
    have : (Z * M * X'⁻¹).val = c • (M.val * (X'⁻¹).val) := by
      rw [Units.val_mul, Units.val_mul, hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [this, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have h3 : e • (θ • Matrix.mulVec (Sm'⁻¹).val zY') = e • (θ' • Matrix.mulVec (Sm⁻¹).val zY) := by
    rw [smul_comm e θ (Matrix.mulVec (Sm'⁻¹).val zY'), hm', smul_comm e θ' (Matrix.mulVec (Sm⁻¹).val zY), hm,
      smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [mul_smul, h2, hg, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h3,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul]
  congr 3
  group

theorem redFn_scalar_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Formalism.L2.DIV.Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (c : E ⊗[F] Formalism.L2.Herm.Af F) (hx : x ∈ Formalism.L2.DIV.St β)
    (hc : x.val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (i₀ : Fin n) :
    ∃ hci : c ∈ Formalism.L2.Herm.intAf F E,
      (Formalism.L2.DIV.resS F PP ⟨c, hci⟩ = 1 → Formalism.L2.DIV.redFn β PP x = 1) := by
  obtain ⟨y, rfl⟩ := hx
  have hy : (Formalism.L2.DIV.intGL F E n y).val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have e1 : Formalism.L2.DIV.intGL F E n y = β⁻¹ * Formalism.L2.DIV.frGL β y * β := by
      simp only [Formalism.L2.DIV.frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, ((y.val i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) i j := fun i j => by
    rw [← hy]; rfl
  have hci : c ∈ Formalism.L2.Herm.intAf F E := by
    have h := hent i₀ i₀
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [← h]; exact (y.val i₀ i₀).2
  refine ⟨hci, fun h1 => ?_⟩
  rw [Formalism.L2.DIV.redFn_frGL]
  apply Units.ext
  ext i j
  have hyij : y.val i j = if i = j then ⟨c, hci⟩ else 0 := by
    apply Subtype.ext
    rw [hent i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  show Formalism.L2.DIV.resS F PP (y.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  rw [hyij, Matrix.one_apply]
  split_ifs <;> simp [h1]


end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedValueCommonConstantsFixedLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_unfoldedValue_commonConstants_fixedLevel : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → GValue (t := t) (v.withCG a) := by
  first | exact @GlobalTheory.SeeSaw.GValAll.gValue_common | exact GlobalTheory.SeeSaw.GValAll.gValue_common | (intros; apply GlobalTheory.SeeSaw.GValAll.gValue_common <;> assumption)
end

