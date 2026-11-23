module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLatticeCongruenceMemConjugateIdealInf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongSelfDual

section Ideals

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem oToS_coe (a : 𝓞 E) : ((Formalism.L2.DIV.oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
    Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E a) := rfl

theorem idS_inf_le (𝔪 𝔫 : Ideal (𝓞 E)) :
    Formalism.L2.DIV.idS F 𝔪 ⊓ Formalism.L2.DIV.idS F 𝔫 ≤ Formalism.L2.DIV.idS F (𝔪 ⊓ 𝔫) := by
  intro x hx
  by_cases hd : 𝔪 ⊔ 𝔫 = ⊥
  · have h1 : 𝔪 = ⊥ := eq_bot_iff.2 (hd ▸ le_sup_left)
    have h2 : 𝔫 = ⊥ := eq_bot_iff.2 (hd ▸ le_sup_right)
    subst h1 h2
    simpa using hx.1
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hd
  obtain ⟨𝔠, h𝔠⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ha)
  have key : Ideal.span {a} * (𝔪 ⊓ 𝔫) = 𝔪 * 𝔫 * 𝔠 := by
    rw [h𝔠, mul_comm (𝔪 ⊔ 𝔫) 𝔠, mul_assoc, Ideal.sup_mul_inf, mul_comm]
  have h1 : Formalism.L2.DIV.oToS F E a * x ∈
      Formalism.L2.DIV.idS F 𝔪 * Formalism.L2.DIV.idS F 𝔫 * Formalism.L2.DIV.idS F 𝔠 := by
    have hfa : Formalism.L2.DIV.oToS F E a ∈ (Formalism.L2.DIV.idS F 𝔪 ⊔ Formalism.L2.DIV.idS F 𝔫) * Formalism.L2.DIV.idS F 𝔠 := by
      have h0 : a ∈ (𝔪 ⊔ 𝔫) * 𝔠 := h𝔠 ▸ Ideal.mem_span_singleton_self a
      have h3 := Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS F E) h0
      unfold Formalism.L2.DIV.idS
      rwa [Ideal.map_mul, Ideal.map_sup] at h3
    have hle : (Formalism.L2.DIV.idS F 𝔪 ⊔ Formalism.L2.DIV.idS F 𝔫) * Formalism.L2.DIV.idS F 𝔠 * Ideal.span {x} ≤
        Formalism.L2.DIV.idS F 𝔪 * Formalism.L2.DIV.idS F 𝔫 * Formalism.L2.DIV.idS F 𝔠 := by
      rw [mul_right_comm, Ideal.sup_mul]
      refine Ideal.mul_mono (sup_le (Ideal.mul_mono le_rfl ((Ideal.span_singleton_le_iff_mem _).2 hx.2)) ?_) le_rfl
      rw [mul_comm (Formalism.L2.DIV.idS F 𝔪)]
      exact Ideal.mul_mono le_rfl ((Ideal.span_singleton_le_iff_mem _).2 hx.1)
    exact hle (Ideal.mul_mem_mul hfa (Ideal.mem_span_singleton_self x))
  have h2 : Formalism.L2.DIV.idS F 𝔪 * Formalism.L2.DIV.idS F 𝔫 * Formalism.L2.DIV.idS F 𝔠 =
      Ideal.span {Formalism.L2.DIV.oToS F E a} * Formalism.L2.DIV.idS F (𝔪 ⊓ 𝔫) := by
    unfold Formalism.L2.DIV.idS
    rw [← Ideal.map_mul, ← Ideal.map_mul, ← key, Ideal.map_mul, Ideal.map_span, Set.image_singleton]
  rw [h2, Ideal.mem_span_singleton_mul] at h1
  obtain ⟨z, hz, hzx⟩ := h1
  have hu : IsUnit ((Formalism.L2.DIV.oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
    rw [oToS_coe]
    have ha1 : algebraMap (𝓞 E) E a ≠ 0 := by
      intro h0; apply ha0; exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).1 h0
    exact (Ne.isUnit ha1).map _
  have hzx' : z = x := by
    apply Subtype.ext
    have h3 := congrArg (fun t : Formalism.L2.Herm.intAf F E => (t : E ⊗[F] Formalism.L2.Herm.Af F)) hzx
    simp only [Subring.coe_mul] at h3
    exact hu.mul_left_cancel h3
  exact hzx' ▸ hz

theorem inId_inf {𝔪 𝔫 : Ideal (𝓞 E)} {x : E ⊗[F] Formalism.L2.Herm.Af F} (h1 : GlobalTheory.FrameIdeal.InId 𝔪 x)
    (h2 : GlobalTheory.FrameIdeal.InId 𝔫 x) : GlobalTheory.FrameIdeal.InId (𝔪 ⊓ 𝔫) x := by
  obtain ⟨s, hs, rfl⟩ := h1
  obtain ⟨t, ht, hts⟩ := h2
  obtain rfl : t = s := Subtype.ext hts
  exact ⟨t, idS_inf_le 𝔪 𝔫 ⟨hs, ht⟩, rfl⟩

theorem inId_neg {I : Ideal (𝓞 E)} {x : E ⊗[F] Formalism.L2.Herm.Af F} (h : GlobalTheory.FrameIdeal.InId I x) :
    GlobalTheory.FrameIdeal.InId I (-x) := by
  have := GlobalTheory.FrameIdeal.inId_mul (t := -1) (neg_mem (one_mem _)) h
  rwa [neg_one_mul] at this

end Ideals

section Forms

variable {A : Type} [CommRing A] {n : ℕ}

theorem hform_dot (τ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform τ J x y = (fun i => τ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_sub_left (τ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    Formalism.UG.hform τ J (x - y) z = Formalism.UG.hform τ J x z - Formalism.UG.hform τ J y z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (τ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    Formalism.UG.hform τ J x (y - z) = Formalism.UG.hform τ J x y - Formalism.UG.hform τ J x z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_unitary (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A) (h : Formalism.UG.cT τ B * J * B = J)
    (x y : Fin n → A) : Formalism.UG.hform τ J (B *ᵥ x) (B *ᵥ y) = Formalism.UG.hform τ J x y := by
  rw [GlobalTheory.DualCompletion.hform_mulVec_left, Matrix.mulVec_mulVec, h, hform_dot]
  rfl

theorem hform_mulVec_right (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A) (a c : Fin n → A) :
    Formalism.UG.hform τ J a (B *ᵥ c) = ∑ k, Formalism.UG.hform τ J a (fun i => B i k) * c k := by
  simp only [hform_dot, Matrix.dotProduct_mulVec]
  rfl

end Forms

variable {D : D7}

theorem conjI_eq (𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SW.conjI 𝔪 = D.host.conj • 𝔪 := by
  show _ = 𝔪.map (MulSemiringAction.toRingHom _ _ D.host.conj)
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [hab]
    show (D.host.conj (b : D.host.E)) = star (b : D.host.E)
    exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    show (D.host.conj (b : D.host.E)) = star (b : D.host.E)
    exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm

theorem inId_hform {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hsd : IsSelfDualC V Λ)
    {β : GL (Fin V.rank) (Lev.EAf D)} (hfr : Formalism.L2.DIV.IsFrame β Λ) {𝔪 : Ideal (𝓞 D.host.E)}
    {a b : Fin V.rank → Lev.EAf D} (ha : a ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hb : b ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) :
    GlobalTheory.FrameIdeal.InId (F := D.host.F) 𝔪
      (Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) a b) := by
  have hc := (GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr 𝔪 b).1 hb
  have e : b = β.1 *ᵥ ((β⁻¹).1 *ᵥ b) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [e, hform_mulVec_right]
  refine GlobalTheory.FrameIdeal.inId_sum _ fun k => GlobalTheory.FrameIdeal.inId_mul ?_ (hc k)
  have hk := GlobalTheory.FrameIdeal.col_mem_hatL hfr k
  rw [Matrix.mulVec_single_one] at hk
  exact GlobalTheory.GramFrame.pair_hatL V.gram Λ (GlobalTheory.FrameIdeal.selfDual_pair hsd) _ _ ha hk


set_option maxHeartbeats 1000000 in
theorem congLev_conj : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (g : GL (Fin V.rank) (Lev.EAf D)), g ∈ congLev D.sp.cm V.gram Λ 𝔪 → g ∈ congLev D.sp.cm V.gram Λ (𝔪 ⊓ D.host.conj • 𝔪) := by
  intro D V Λ hsd 𝔪 g hg
  by_cases h𝔪 : 𝔪 = ⊥
  · subst 𝔪
    simpa only [bot_inf_eq] using hg
  rw [GlobalTheory.ChiGrid.mem_congLev] at hg ⊢
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨β, hfr⟩ : ∃ β : GL (Fin V.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame β Λ :=
    GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ hsd.1.fg
      (Submodule.IsFullLattice.span_eq_top (self := GlobalTheory.AdIsom.selfDual_isFullLattice hsd))
  refine ⟨g1, g2, fun y hy => ?_⟩
  have hm := g3 y hy
  have hU : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) g.1 *
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * g.1 =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := g1
  have hc : g.1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.SW.conjI 𝔪 • Λ) := by
    refine (GlobalTheory.FrameIdeal.mem_hatL_conjI_iff_hform D V Λ hsd β hfr 𝔪 h𝔪 _).2 fun j => ?_
    have hx : (β.1)ᵀ j ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
      have h0 := GlobalTheory.FrameIdeal.col_mem_hatL (D := D) (β := β) (Λ := Λ) hfr j
      rwa [Matrix.mulVec_single_one] at h0
    have e : Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) (g.1 *ᵥ y - y) (fun c => β.1 c j) =
        -Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
          (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) (g.1 *ᵥ y)
          (g.1 *ᵥ (β.1)ᵀ j - (β.1)ᵀ j) := by
      rw [hform_sub_left, hform_sub_right, hform_unitary _ _ _ hU]
      have : (fun c => β.1 c j) = (β.1)ᵀ j := rfl
      rw [this]; ring
    rw [e]
    exact inId_neg (inId_hform hsd hfr ((g2 y).1 hy) (g3 _ hx))
  rw [conjI_eq] at hc
  rw [GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr] at hm hc ⊢
  exact fun i => inId_inf (hm i) (hc i)

end GlobalTheory.CongSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFixedOfFixesPureTensorsVacuaOutside
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

theorem GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))), M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) →
    (∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ ψ : (Fin n × Fin d → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) ψ → ψ = M.vac v := by
  intro F E _ _ _ _ _ σ n d Y Wd M om v k S hvac hstd hfix ψ hψ
  let ind : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1

  let φ := Function.update ind v (M.vac v)
  have hφv : φ v = M.vac v := by simp [φ]
  have hφw : ∀ w, w ≠ v → φ w = ind w := fun w h => by simp [φ, h]
  have hφev : ∀ᶠ w in Filter.cofinite,
      φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton v).subset fun w hw => ?_
    by_contra hne
    exact hw (hφw w hne)
  have hSB : ∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; rw [hφv]; exact hvac
    · rw [hφw w h]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F (Fin n × Fin d)
  obtain ⟨r, hrinv, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφev
  have hupd : ∀ ψ₀, Function.update φ v ψ₀ = Function.update ind v ψ₀ :=
    fun ψ₀ => Function.update_idem _ _ _

  have hfixφ : om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    refine hfix f φ hSB fun w hw => ?_
    by_cases h : w = v
    · subst h; exact hφv
    · rw [hφw w h, hstd w hw]
  have hpv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    rw [hrt, hupd]
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest
    refine ⟨hrinv, ?_⟩
    rw [hpv]
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hφev
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) ψ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    rw [← hψ r hRest, hpv, hfixφ]

  have hr0 : r 0 ≠ 0 := by
    have h1 := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at h1
    rw [h1, hupd]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have e1 : (fun i : Fin n × Fin d => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : Fin n × Fin d → AF F) i)) = 0 := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : Fin n × Fin d → AF F) i).1 = 0
      exact map_zero _
    have e2 : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), Function.update ind v (fun _ => 1) w
        (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1 := by
      intro w
      by_cases h : w = v
      · subst h; simp
      · rw [Function.update_of_ne h]
        show Set.indicator {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
          (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1
        rw [Set.indicator_of_mem]
        · rfl
        · simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
          exact fun _ => zero_mem _
    rw [e1, finprod_congr e2, finprod_one, mul_one]
    exact hf
  funext y
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (fun i => GlobalTheory.EmbChart.atPlace v (y i)) := by
    intro u hu
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hrz : r (fun i => GlobalTheory.EmbChart.atPlace v (y i)) = r 0 := by
    simpa using hrinv 0 _ hz
  have h2 := congrFun key (fun i => GlobalTheory.EmbChart.atPlace v (y i))
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.EmbChart.evFin_atPlace, hrz] at h2
  exact mul_right_cancel₀ hr0 h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionOMemLatticeOOfIntegralCombinations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.LatMoveGen

variable {D : D7}

theorem gram_mul_inv (V : HSp D) (g : Formalism.L2.Theta.GA D V) :
    V.gram.map (incA D) * Formalism.L2.Theta.mt V g⁻¹ =
      ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) := by
  have h : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) :=
    (g : HR (AF D.host.F) D.sp.cm.sig V.gram).2
  have h2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    rw [← GlobalTheory.LatMoveStd.mt_mul'', mul_inv_cancel, GlobalTheory.LatMoveStd.mt_one'']
  calc V.gram.map (incA D) * Formalism.L2.Theta.mt V g⁻¹
      = (((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g) * Formalism.L2.Theta.mt V g⁻¹ := by rw [h]
    _ = _ := by rw [Matrix.mul_assoc _ (Formalism.L2.Theta.mt V g), h2, Matrix.mul_one]

theorem row_move (V : HSp D) (g : Formalism.L2.Theta.GA D V) (s : Fin V.rank → D.host.E) (j : Fin V.rank) :
    ∑ m, incA D (∑ k, star (s k) * V.gram k m) * Formalism.L2.Theta.mt V g⁻¹ m j =
      ∑ m, cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m) * incA D (V.gram m j) := by
  have e1 : (fun m => incA D (∑ k, star (s k) * V.gram k m)) =
      (fun k => cA D (incA D (s k))) ᵥ* V.gram.map (incA D) := by
    funext m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply, GlobalTheory.FinPl.FrameLat.cA_incA]
  have e2 : (fun m => cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m)) =
      (Formalism.L2.Theta.mt V g).map (cA D) *ᵥ fun k => cA D (incA D (s k)) := by
    funext m
    exact RingHom.map_mulVec (cA D) _ _ m
  have lhs : ∑ m, incA D (∑ k, star (s k) * V.gram k m) * Formalism.L2.Theta.mt V g⁻¹ m j =
      ((fun m => incA D (∑ k, star (s k) * V.gram k m)) ᵥ* Formalism.L2.Theta.mt V g⁻¹) j := rfl
  have rhs : ∑ m, cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m) * incA D (V.gram m j) =
      ((fun m => cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m)) ᵥ* V.gram.map (incA D)) j := rfl
  rw [lhs, rhs, e1, e2, Matrix.vecMul_vecMul, gram_mul_inv, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]

end GlobalTheory.LatMoveGen

namespace GlobalTheory.LatMoveGen

variable {D : D7}

theorem act_gen_apply (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T) (α : Af D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    actO S T g h (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) i j =
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) * ((Formalism.L2.Theta.mt T h *ᵥ fun k => incA D (t k)) i *
        ∑ m, cA D ((Formalism.L2.Theta.mt S g *ᵥ fun k => incA D (s k)) m) * incA D (S.gram m j)) := by
  rw [← row_move]
  simp only [actO, Matrix.mul_apply, Matrix.of_apply, GlobalTheory.LatMoveStd.gen_eq]
  simp only [ Matrix.mul_apply, Matrix.of_apply, GlobalTheory.LatMoveStd.gen_eq, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem comb_apply (S T : HSp D) (α : Af D.host.F) (a : D.host.E) {m m' : ℕ} (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin T.rank → D.host.E)
    (β' : Fin m' → Formalism.L2.Theta.AE D) (b' : Fin m' → Fin S.rank → D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    (∑ p, ∑ q, (β p * cA D (β' q)) • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a * b p i * ∑ k, star (b' q k) * S.gram k j)) : WO S T) i j =
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) * ((∑ p, β p * incA D (b p i)) *
        ∑ k, cA D (∑ q, β' q * incA D (b' q k)) * incA D (S.gram k j)) := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, GlobalTheory.LatMoveStd.gen_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul,
    GlobalTheory.FinPl.FrameLat.cA_incA, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_)
  ring

end GlobalTheory.LatMoveGen

namespace GlobalTheory.LatMoveGen


set_option synthInstance.maxHeartbeats 400000 in
theorem actO_mem_latO : ∀ {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    (∀ s ∈ AS, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin S.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BS) ∧
      ∀ i, finPart D ((mt S g *ᵥ fun k => incA D (s k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    (∀ t ∈ AT, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin T.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BT) ∧
      ∀ i, finPart D ((mt T h *ᵥ fun k => incA D (t k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    ∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D S T g h AS BS AT BT hS hT w hw
  let Ψ : WO S T →+ WO S T :=
    { toFun := actO S T g h
      map_zero' := by simp only [actO, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul] }
  have key : latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True) ≤
      (latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨m', β', b', hβ', hb', hu⟩ := hS s hs
    obtain ⟨m, β, b, hβ, hb, hv⟩ := hT t ht
    have e : actO S T g h (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
        ∑ p, ∑ q, (β p * cA D (β' q)) • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a * b p i * ∑ k, star (b' q k) * S.gram k j) : WO S T) := by
      ext i j
      rw [act_gen_apply, comb_apply, mul_comm, mul_comm (pairA D.host.F 0 α ⊗ₜ[D.host.F] a),
        GlobalTheory.LatticeStable.mul_pair_tmul, GlobalTheory.LatticeStable.mul_pair_tmul]
      congr 2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_sum, GlobalTheory.FinPl.FrameLat.finPart_cA, hv, hu]
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show actO S T g h _ ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True)
    rw [e]
    refine sum_mem fun p _ => sum_mem fun q _ => ?_
    refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _ (AddSubgroup.subset_closure
      ⟨α, hα, fun _ h => absurd trivial h, a, ha, b' q, hb' q, b p, hb p, rfl⟩)
    rw [map_mul]
    exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE (hβ p) ((GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 (hβ' q))
  exact key hw

end GlobalTheory.LatMoveGen
end
end

