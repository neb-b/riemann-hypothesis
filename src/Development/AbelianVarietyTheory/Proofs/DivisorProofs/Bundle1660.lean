module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeightEqAbsInfType
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SplitWeight

theorem exps_eq_zero {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ)
    (h1 : Function.Injective φ) (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) (c : I → ℤ)
    (h : ∀ k : L, k ≠ 0 → ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ c i = 1) : c = 0 := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := GlobalTheory.HalfIntChars.emb_mul_indep σ hσ (Sum.elim c (-c)) (fun k hk => by
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have e3 := congrArg (· ^ 2) (h k hk)
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (c i), zpow_mul, zpow_natCast,
      GlobalTheory.HalfIntChars.unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg])
  funext i
  have := congrFun this (Sum.inl i)
  simpa using this

theorem embTau_inj (D : D7) : Function.Injective (Formalism.L2.Host.embTau D) := fun i j h =>
  D.eTau.injective (GlobalTheory.HalfIntChars.embPsi_inj D.host h)

theorem embTau_ne_conj (D : D7) (i j : D.what₂.Tau) :
    Formalism.L2.Host.embTau D i ≠ (starRingEnd ℂ).comp (Formalism.L2.Host.embTau D j) :=
  GlobalTheory.HalfIntChars.embPsi_ne_conj D.host (D.eTau i) (D.eTau j)

theorem prod_eq_one {D : D7} {N : ℕ} (χ : HeckeU D N) (e : ℤ) (χ' : HChar D.host.E) (k : D.what₂.Tau → ℤ)
    (hf : ∀ x, χ.f x ^ e = χ'.1 (finIdl D x)) (hk : χ'.HasInf (Formalism.L2.Host.embTau D) k)
    (a : D.host.E) (ha : a ≠ 0) :
    ∏ τ, (Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ)) ^ (e * χ.n τ - k τ) = 1 := by
  set u := Units.mk0 a ha
  set φ := Formalism.L2.Host.embTau D
  have hne : ∀ τ, φ τ a ≠ 0 := fun τ => by simpa using ha
  have hu : ∀ τ, φ τ a / ((‖φ τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
    div_ne_zero (hne τ) (by exact_mod_cast norm_ne_zero_iff.2 (hne τ))
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := χ'.2.2 u
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, ← hf] at hB
  have hB' : ((χ'.inf u : ℂˣ) : ℂ) * ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e = 1 := by
    have := congrArg Units.val hB
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] at this
    exact this
  rw [hk u] at hB'
  set X := ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ)
  have hX : X ≠ 0 := by simp [X]
  have hX' : X = (∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ))⁻¹ := eq_inv_of_mul_eq_one_left hA
  rw [hX', inv_zpow', ← Finset.prod_zpow] at hB'
  simp_rw [zpow_sub₀ (hu _), Finset.prod_div_distrib, mul_comm e, zpow_mul]
  rw [div_eq_one_iff_eq]
  · have h2 := eq_inv_of_mul_eq_one_left hB'
    have hua : (u : D.host.E) = a := rfl
    rw [hua] at h2
    rw [h2, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [zpow_neg, inv_inv]
  · exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hu τ)

theorem abs_weight_eq_abs_infType : ∀ {D : D7} {N : ℕ} (χ : HeckeU D N) (e : ℤ) (χ' : HChar D.host.E)
    (k : D.what₂.Tau → ℤ), (e = 1 ∨ e = -1) → (∀ x, χ.f x ^ e = χ'.1 (finIdl D x)) →
    χ'.HasInf (Formalism.L2.Host.embTau D) k → ∀ τ, |χ.n τ| = |k τ| := by
  intro D N χ e χ' k he hf hk τ
  have hc := exps_eq_zero (Formalism.L2.Host.embTau D) (embTau_inj D) (embTau_ne_conj D)
    (fun τ => e * χ.n τ - k τ) (fun a ha => prod_eq_one χ e χ' k hf hk a ha)
  have h := congrFun hc τ
  simp only [Pi.zero_apply, sub_eq_zero] at h
  rw [← h]
  rcases he with rfl | rfl <;> simp

end GlobalTheory.SplitWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPureTensorFixedByOpenFiniteHeisenberg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

open Topology Filter

theorem pureA_fixed_fin :
    ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
      ∃ M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m ∈ M, ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ,
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 F m) (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  intro F _ _ ψ hψ κ _ g hg
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.HeisSchA.nonarch_pi
  let χ := GlobalTheory.HeisSchA.finChar ψ
  have hL : IsOpen {a | χ a = 1} := (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ).isOpen_fiber 1
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2

  obtain ⟨V0, hV0⟩ : ∃ V0 : OpenAddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      ∀ u ∈ V0, ∀ v ∈ V0, χ (c * (u ⬝ᵥ v)) = 1 := by
    have hcont : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        c * (p.1 ⬝ᵥ p.2) :=
      continuous_const.mul (continuous_fst.dotProduct continuous_snd)
    have h0 : ∀ᶠ p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) in 𝓝 0 ×ˢ 𝓝 0,
        χ (c * (p.1 ⬝ᵥ p.2)) = 1 := by
      rw [← nhds_prod_eq]
      refine hcont.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_)
      simp [χ]
    obtain ⟨s, hs, hss⟩ := (Filter.eventually_prod_self_iff (r := fun a b => χ (c * (a ⬝ᵥ b)) = 1)).mp h0
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean s hs
    exact ⟨V, fun u hu v hv => hss u (hV hu) v (hV hv)⟩

  have hloc : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∃ V : OpenAddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      ∀ a ∈ V, ∀ u ∈ V, g (y + a + u) = g y ∧ χ ((y + a) ⬝ᵥ u) = 1 := by
    intro y
    have c1 : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        y + p.1 + p.2 := (continuous_const.add continuous_fst).add continuous_snd
    have c2 : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        (y + p.1) ⬝ᵥ p.2 := (continuous_const.add continuous_fst).dotProduct continuous_snd
    have h0 : ∀ᶠ p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) in 𝓝 0 ×ˢ 𝓝 0,
        g (y + p.1 + p.2) = g y ∧ χ ((y + p.1) ⬝ᵥ p.2) = 1 := by
      rw [← nhds_prod_eq]
      refine Filter.Eventually.and (c1.continuousAt.preimage_mem_nhds ((hg.1.isOpen_fiber (g y)).mem_nhds ?_))
        (c2.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_))
      · simp
      · simp [χ]
    obtain ⟨s, hs, hss⟩ := (Filter.eventually_prod_self_iff
      (r := fun a u => g (y + a + u) = g y ∧ χ ((y + a) ⬝ᵥ u) = 1)).mp h0
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean s hs
    exact ⟨V, fun a ha u hu => hss a (hV ha) u (hV hu)⟩
  choose V hV using hloc
  obtain ⟨t, -, htK⟩ := (hg.2 : IsCompact (tsupport g)).elim_nhds_subcover
    (fun y => {z | z - y ∈ (V y : Set (κ → FiniteAdeleRing (𝓞 F) F))}) (fun y _ => by
      refine (continuous_sub_right y).continuousAt.preimage_mem_nhds ?_
      rw [sub_self]
      exact (V y).isOpen.mem_nhds (V y).zero_mem)
  let M0 : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (V0 : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) ⊓ ⨅ y ∈ t, (V y : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
  have hM0 : ∀ u ∈ M0, u ∈ V0 ∧ ∀ y ∈ t, u ∈ V y := fun u hu => by
    simp only [M0, AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hu
    exact ⟨hu.1, hu.2⟩
  have hM0open : IsOpen (M0 : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
    refine M0.isOpen_of_mem_nhds (g := 0) ?_
    refine Filter.mem_of_superset (Filter.inter_mem (V0.isOpen.mem_nhds V0.zero_mem)
      ((Filter.biInter_finset_mem t).2 fun y _ => (V y).isOpen.mem_nhds (V y).zero_mem)) ?_
    intro u hu
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hu
    simp only [M0, SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
    exact ⟨hu.1, hu.2⟩
  have hcov : ∀ y ∈ tsupport g, ∀ u ∈ M0, g (y + u) = g y ∧ ∀ v ∈ M0, χ (y ⬝ᵥ v) = 1 := by
    intro y hy u hu
    obtain ⟨z, hz, hyz⟩ : ∃ z ∈ t, y - z ∈ V z := by simpa using htK hy
    have e : z + (y - z) = y := by abel
    have h1 := hV z (y - z) hyz u ((hM0 u hu).2 z hz)
    have h2 := hV z (y - z) hyz 0 (V z).zero_mem
    rw [e] at h1 h2
    rw [add_zero] at h2
    refine ⟨h1.1.trans h2.1.symm, fun v hv => ?_⟩
    have h3 := hV z (y - z) hyz v ((hM0 v hv).2 z hz)
    rw [e] at h3
    exact h3.2
  have hinv : ∀ u ∈ M0, ∀ y, g (y + u) = g y := by
    intro u hu y
    by_cases hy : y ∈ tsupport g
    · exact (hcov y hy u hu).1
    by_cases hy' : y + u ∈ tsupport g
    · have := (hcov (y + u) hy' (-u) (M0.neg_mem hu)).1
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']
  refine ⟨M0.prod M0, by rw [AddSubgroup.coe_prod]; exact hM0open.prod hM0open, ?_⟩
  rintro ⟨u, v⟩ hm f
  rw [AddSubgroup.mem_prod] at hm
  obtain ⟨hu, hv⟩ := hm
  funext x
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA, finE2]
  have harg : x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v) =
      ((0 : InfiniteAdeleRing F), (fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) := by
    have hp1 : ∀ (w : κ → FiniteAdeleRing (𝓞 F) F) (i : κ), GlobalTheory.HeisSchA.p1 (finE F w i) = 0 := fun _ _ => rfl
    have hp2 : ∀ (w : κ → FiniteAdeleRing (𝓞 F) F) (i : κ), GlobalTheory.HeisSchA.p2 (finE F w i) = w i := fun _ _ => rfl
    refine Prod.ext ?_ ?_
    · change GlobalTheory.HeisSchA.p1 (x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v)) = 0
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_mul, dotProduct, map_sum, hp1, mul_zero, Finset.sum_const_zero, add_zero]
    · change GlobalTheory.HeisSchA.p2 (x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_mul, dotProduct, map_sum, hp2]
      rfl
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + finE F u) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    rw [show ((x + finE F u) i).1 = (x i).1 from add_zero (x i).1]
  have hgx : (fun i => ((x + finE F u) i).2) = (fun i => (x i).2) + u := by
    funext i
    rfl
  rw [harg, hf, hgx, hinv u hu]
  by_cases h0 : g (fun i => (x i).2) = 0
  · rw [h0]
    ring
  · have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport g h0
    have e1 := (hcov _ hy u hu).2 v hv
    have e2 := hV0 u (hM0 u hu).1 v (hM0 v hv).1
    have : ψ ((0 : InfiniteAdeleRing F), (fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) = 1 := by
      change χ ((fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) = 1
      rw [AddChar.map_add_eq_mul, e1, e2, one_mul]
    rw [this, one_mul]

end GlobalTheory.WeilAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun t : κ → Fv F v => Φ (fun i => GlobalTheory.LatVac.liftV v (t i))) ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  first | exact @GlobalTheory.LatVac.restrict_liftV_mem_SB | exact GlobalTheory.LatVac.restrict_liftV_mem_SB | (intros; apply GlobalTheory.LatVac.restrict_liftV_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSupportCompactInvariance
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

noncomputable section

namespace GlobalTheory.FinLocSchA

open GlobalTheory.WeilM

theorem exists_open_addStab {X : Type} [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {g : X → ℂ} (hg : g ∈ SB X) :
    ∃ K : AddSubgroup X, IsOpen (K : Set X) ∧ ∀ z, ∀ k ∈ K, g (z + k) = g z := by
  let K : AddSubgroup X :=
    { carrier := {k | ∀ z, g (z + k) = g z}
      zero_mem' := by intro z; simp
      add_mem' := by
        intro a b ha hb z
        rw [← add_assoc, hb, ha]
      neg_mem' := by
        intro a ha z
        have := ha (z + -a)
        simpa using this.symm }
  refine ⟨K, ?_, fun z k hk => hk z⟩
  have h1 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + k) = g z := by
    apply IsCompact.eventually_forall_of_forall_eventually hg.2
    intro z _
    have a1 : IsLocallyConstant (fun p : X × X => g (p.2 + p.1)) :=
      hg.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun p : X × X => g p.2) :=
      hg.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (0, z), a2.eventually_eq (0, z)] with p hp1 hp2
    simp only [hp1, hp2, add_zero]
  have h2 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + -k) = g z := by
    have : Filter.Tendsto (fun k : X => -k) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact this.eventually h1
  apply AddSubgroup.isOpen_of_mem_nhds K (g := 0)
  filter_upwards [h1, h2] with k hk1 hk2
  intro z
  by_cases hz : z ∈ tsupport g
  · exact hk1 z hz
  · by_cases hz' : z + k ∈ tsupport g
    · simpa using (hk2 _ hz').symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

theorem compact_support_locally_constant_fin : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨K, hKo, hK⟩ := exists_open_addStab hg
    refine ⟨tsupport g, K, hg.2, hKo, K.zero_mem, ?_, ?_⟩
    · intro x hx
      by_contra hc
      apply hx
      simp only [pureA]
      rw [image_eq_zero_of_notMem_tsupport hc, mul_zero]
    · intro x x' h1 h2
      simp only [pureA, ← h1]
      congr 1
      have e2 : (fun i => (x' i).2) = (fun i => (x i).2) + (fun i => (x' i).2 - (x i).2) := by
        ext i; simp
      rw [e2]
      exact hK _ _ h2
  | zero =>
    refine ⟨∅, Set.univ, isCompact_empty, isOpen_univ, trivial, ?_, ?_⟩
    · intro x hx; exact absurd rfl hx
    · intro x x' _ _; rfl
  | add Φ Ψ _ _ ihΦ ihΨ =>
    obtain ⟨C₁, K₁, hC₁, hK₁, h0₁, hs₁, hi₁⟩ := ihΦ
    obtain ⟨C₂, K₂, hC₂, hK₂, h0₂, hs₂, hi₂⟩ := ihΨ
    refine ⟨C₁ ∪ C₂, K₁ ∩ K₂, hC₁.union hC₂, hK₁.inter hK₂, ⟨h0₁, h0₂⟩, ?_, ?_⟩
    · intro x hx
      by_cases h : Φ x = 0
      · right; apply hs₂ x; intro h'; apply hx; simp [h, h']
      · left; exact hs₁ x h
    · intro x x' h1 h2
      simp only [Pi.add_apply, hi₁ x x' h1 h2.1, hi₂ x x' h1 h2.2]
  | smul a Φ _ ih =>
    obtain ⟨C, K, hC, hK, h0, hs, hi⟩ := ih
    refine ⟨C, K, hC, hK, h0, ?_, ?_⟩
    · intro x hx
      apply hs x
      intro h; apply hx; simp [h]
    · intro x x' h1 h2
      simp only [Pi.smul_apply, hi x x' h1 h2]

end GlobalTheory.FinLocSchA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SplitAdeleTrace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul_comp (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]


omit [NumberField F] [NumberField E] in
theorem trace_baseChange_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem add_conj_eq_trace {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) :
    x + σ x = algebraMap F E (Algebra.trace F E x) := by
  classical
  have hc := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (by ext y; simp [GlobalTheory.AdelicU.cm_conj_conj h])
    (by ext y; simp [GlobalTheory.AdelicU.cm_conj_conj h])
  have hs : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h1
    obtain ⟨y, hy⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne h
    exact hy (DFunLike.congr_fun h1 y).symm
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h.2.2.1]
  rw [trace_eq_sum_automorphisms, hu, Finset.sum_pair hs]
  rfl

theorem trace_at_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v)
    (z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z →
    Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z =
      GlobalTheory.LatVac.liftV v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ z + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) z) := by
  intro F E _ _ _ _ _ σ hcm v τ z hz
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  set l : AF F := GlobalTheory.LatVac.liftV v 1 with hl
  have hz1 : z = l • z := by
    have h0 := hz (1 - l) (by rw [map_sub, map_one, hl, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  have hpiW : ∀ (t : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (l • w) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t w := by
    intro t w
    rw [Algebra.smul_def, map_mul]
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (algebraMap (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) l) = 1 := by
      change evFin F v l * t 1 = 1
      rw [hl, GlobalTheory.LatVac.evFin_liftV, map_one, one_mul]
    rw [this, one_mul]
  have key : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (l • w) =
      GlobalTheory.LatVac.liftV v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ w + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, ← map_add (f := _)]; congr 1; simp only [map_add (f := _)]; ring
    | tmul b e =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, trace_baseChange_tmul, mul_assoc, liftV_one_mul_comp, map_mul,
        AlgHom.commutes]
      congr 1
      change evFin F v b * algebraMap F (Fv F v) (Algebra.trace F E e) = evFin F v b * τ e + evFin F v b * τ (σ e)
      rw [← mul_add, ← map_add (f := _), add_conj_eq_trace hcm, AlgHom.commutes]
  rw [hz1, key, hpiW, hpiW]

end GlobalTheory.SplitAdeleTrace
end
end

