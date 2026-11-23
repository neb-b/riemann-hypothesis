module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0710
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0712
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0716
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0570
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0562
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0566
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0715
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.E45FinalGluing
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem eFinalGlue_of (hCS : ConvStrip) (hCC : ConvComp) (hFS : FactorStep) (hLL : LimLists) (hOS : OneStep)
    (hFL : FactorLim) (hMC : MCloseFacts) (hPE : PairEmb) (hPS : PairSlices) (hST : SliceType) : InfinitesimalCharacterGlue := by
  intro hE3 hSep hLim hGraft hTw hTr hLV hAD hUn hInf E _ _ _ a b W₁ W₂ hW₁ hW₂
  obtain ⟨Ωs₁, hΩs₁, S₁⟩ := hFS hSep E a W₁ hW₁
  obtain ⟨Ωs₂, hΩs₂, S₂⟩ := hFS hSep E b W₂ hW₂
  obtain ⟨Ωf₁, hΩf₁, X₁⟩ := hLL hLim hTw E a Ωs₁ hΩs₁
  obtain ⟨Ωf₂, hΩf₂, X₂⟩ := hLL hLim hTw E b Ωs₂ hΩs₂
  refine ⟨Ωf₁, Ωf₂, hΩf₁, hΩf₂, fun K₁ K₂ hK₁ hK₂ => ?_⟩
  obtain ⟨Θs₁, hΘs₁, F₁⟩ := S₁ K₁ hK₁
  obtain ⟨Θs₂, hΘs₂, F₂⟩ := S₂ K₂ hK₂
  obtain ⟨Θf₁, hΘf₁, P₁⟩ := X₁ Θs₁ hΘs₁
  obtain ⟨Θf₂, hΘf₂, P₂⟩ := X₂ Θs₂ hΘs₂
  refine ⟨Θf₁, Θf₂, hΘf₁, hΘf₂, ?_⟩
  intro D ι _ M m₁ m₂ n₁ n₂ C lam lam₀ f hC hRep hcont hne hL hWL hTy hs1 hs2 ha1 ha2 hi1 hi2 heig hconv hR1 hR2 hgap hlam
  have hfar : ∀ᶠ k in atTop, ∀ τ, MClose (1 / 8) (m₁ k τ) (n₁ τ) ∧ MClose (1 / 8) (m₂ k τ) (n₂ τ) :=
    Filter.eventually_all.2 fun τ => hconv τ (1 / 8) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hfar
  have h3 := fun k => hE3 E a b D ι M (f k) K₁ K₂ W₁ W₂ (m₁ k) (m₂ k) hK₁ hK₂ hW₁ hW₂ (hcont k) (hL k) (hWL k)
    (hTy k) (hs1 k) (hs2 k) (ha1 k) (ha2 k) (hi1 k) (hi2 k)
  have hone := fun k => hOS E a b ι K₁ K₂ W₁ W₂ Θs₁ Θs₂ Ωs₁ Ωs₂ (f (k + k₀)) (m₁ (k + k₀)) (m₂ (k + k₀)) hW₁ hW₂ F₁ F₂
    (hne _) (hTy _) (hs1 _) (hs2 _) (h3 _).2.2.1 (h3 _).2.2.2.1 (h3 _).2.2.2.2.1 (h3 _).2.2.2.2.2.1
    (h3 _).2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.2.1
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).1 (hgap τ).1)
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).2 (hgap τ).2)
    (h3 _).2.2.2.2.2.2.2.2.2.2
  choose t₁ t₂ G ψ₁ ψ₂ hr₁ hr₂ hg₁ hg₂ hl₁ hl₂ hG0 hGm hGt hGe hp₁ hp₁0 hc₁ hp₂ hp₂0 hc₂ using hone
  have hB : ∀ n : (E →+* ℂ) → Multiset ℂ, ∃ B : ℝ, ∀ τ, ∀ y ∈ n τ, ‖y‖ ≤ B := fun n => by
    classical
    obtain ⟨B, hB⟩ := ((Finset.univ.biUnion fun τ => (n τ).toFinset).image norm).finite_toSet.bddAbove
    refine ⟨B, fun τ y hy => hB ?_⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Multiset.mem_toFinset]
    exact ⟨y, ⟨τ, hy⟩, rfl⟩
  obtain ⟨B₁, hB₁⟩ := hB n₁
  obtain ⟨B₂, hB₂⟩ := hB n₂
  obtain ⟨φ₁, t₁', s₁, hφ₁, hC₁, hs₁R, hs₁G, hs₁L, hD₁, hI₁, hE₁⟩ := hFL hTr hGraft hInf E Θs₁ Θf₁ Ωs₁ Ωf₁ a t₁ ψ₁
    (fun k => m₁ (k + k₀)) n₁ (B₁ + 1 / 8) P₁ hRep hr₁ hg₁ hl₁ hp₁ hp₁0 hc₁
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (k + k₀) (by omega) τ).1 (hB₁ τ))
    (fun τ ε hε => ((tendsto_add_atTop_nat k₀).eventually (hconv τ ε hε)).mono fun _ h => h.1)
  obtain ⟨φ₂, t₂', s₂, hφ₂, hC₂, hs₂R, hs₂G, hs₂L, hD₂, hI₂, hE₂⟩ := hFL hTr hGraft hInf E Θs₂ Θf₂ Ωs₂ Ωf₂ b
    (fun k => t₂ (φ₁ k)) (fun k => ψ₂ (φ₁ k))
    (fun k => m₂ (φ₁ k + k₀)) n₂ (B₂ + 1 / 8) P₂ hRep (fun k => hr₂ _) (fun k => hg₂ _) (fun k => hl₂ _)
    (fun k => hp₂ _) (fun k => hp₂0 _) (fun k => hc₂ _)
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (φ₁ k + k₀) (by omega) τ).2 (hB₂ τ))
    (fun τ ε hε => (((tendsto_add_atTop_nat k₀).comp hφ₁.tendsto_atTop).eventually (hconv τ ε hε)).mono fun _ h => h.2)
  have hstab : ∀ {N : ℕ} {t : Tr E N}, t.Good → IsStable t.space := fun h => hTr E _ _ (disc_stable (good_disc h))
  have hG' := fun k => hPE E a b ι K₁ K₂ W₁ W₂ (t₁ (φ₁ (φ₂ k))).space (t₁' (φ₂ k)).space (t₂ (φ₁ (φ₂ k))).space (t₂' k).space
    (G (φ₁ (φ₂ k))) hW₁ hW₂ (hstab (hg₁ _)) (hstab (hg₂ _)) (hE₁ _) (hE₂ _) (hG0 _) (hGm _) (hGt _)
  choose G' hG'0 hG'm hG't hG'e using hG'
  have hCC₁ := (hCS E a _ _).1 (hCC E a _ _ φ₂ hC₁ hφ₂)
  have hCC₂ := (hCS E b _ _).1 hC₂
  obtain ⟨F, hF0, hFm, hFt, hFe⟩ := hLV hAD E a b ι (fun k => t₁' (φ₂ k)) t₂' s₁ s₂ K₁ K₂ W₁ W₂ C
    (fun k => lam (φ₁ (φ₂ k) + k₀)) lam₀ G' hK₁ hK₂ hW₁ hW₂ hC hs₁G hs₂G (fun k => hD₁ _) hD₂ hCC₁.1 hCC₂.1 hCC₁.2 hCC₂.2
    hG'0 hG'm hG't (fun k h hh => hG'e k h _ (hGe _ h _ (heig _ h hh)))
    (fun h hh => (hlam h hh).comp ((tendsto_add_atTop_nat k₀).comp (hφ₁.comp hφ₂).tendsto_atTop))
  obtain ⟨i, hi⟩ : ∃ i, F i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hF0 (funext hcon)
  obtain ⟨x, hx⟩ : ∃ x, F i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hi (funext hcon)
  have hsl := hPS E a b _ _ (F i) (hFm i)
  have hn₁ : sl₁ (F i) x.2 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.1 x.2).2 x.1
    rw [h] at this
    exact this.symm)
  have hn₂ : sl₂ (F i) x.1 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.2 x.1).2 x.2
    rw [h] at this
    exact this.symm)
  have hb₁ : s₁.space ≠ ⊥ := fun h => hn₁ (by simpa [h] using (hsl.1 x.2).1)
  have hb₂ : s₂.space ≠ ⊥ := fun h => hn₂ (by simpa [h] using (hsl.2 x.1).1)
  exact ⟨s₁, s₂, F, hs₁G, hs₂G, hUn E a s₁ n₁ hs₁G hb₁ hI₁ hR1, hUn E b s₂ n₂ hs₂G hb₂ hI₂ hR2, hs₁L, hs₂L,
    hI₁, hI₂, hF0, hFm, hFt, hFe⟩

theorem eFinalGlue : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue :=
  have hPS := _root_.GlobalTheory.CompanionTheory.EGlue.pairSlices
  have hP1 := _root_.GlobalTheory.CompanionTheory.EGlue.TensorOne.pairStep₁_of_slices hPS
  have hP2 := _root_.GlobalTheory.CompanionTheory.EGlue.pairStep₂ hPS
  have hCE := _root_.GlobalTheory.CompanionTheory.EGlue.capEquiv
  have hDI := _root_.GlobalTheory.CompanionTheory.EGlue.discInf
  have hTI := _root_.GlobalTheory.CompanionTheory.EGlue.Gl0.topInf
  have hIE := _root_.GlobalTheory.CompanionTheory.EGlue.infOfEq_holds
  have hCS := _root_.GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip
  have hCC := _root_.GlobalTheory.CompanionTheory.EGlue.convComp_proved
  have hMC := _root_.GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds
  eFinalGlue_of hCS hCC _root_.GlobalTheory.CompanionTheory.EGlue.factorStep_holds (_root_.GlobalTheory.CompanionTheory.EGlue.limLists hCS _root_.GlobalTheory.CompanionTheory.EGlue.convShift_holds hCC)
    (_root_.GlobalTheory.CompanionTheory.EGlue.OneStepProof.oneStep_of_parts hPS _root_.GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds _root_.GlobalTheory.CompanionTheory.EGlue.pairFD_holds _root_.GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main hP1 hP2 _root_.GlobalTheory.CompanionTheory.EGlue.hullGen hCE)
    (_root_.GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts hCC (_root_.GlobalTheory.CompanionTheory.EGlue.LimT.limTrees hCC) (_root_.GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound hDI hTI hIE) (_root_.GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf hDI hTI) hIE hCE hMC)
    hMC (_root_.GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps hPS hP1 hP2) hPS _root_.GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticePeriodicity
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

open ValuativeRel Topology Uniformity GlobalTheory.CompanionTheory.BZPsiPG.FibKer

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_inv_integer_subset {W : Set k} (hW : W ∈ 𝓝 (0 : k)) :
    ∃ c : k, c ≠ 0 ∧ ∀ x, c * x ∈ 𝒪[k] → x ∈ W := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hW
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [map_zero] at ha
    exact γ.ne_zero ha.symm
  have hd : a * w ≠ 0 := mul_ne_zero ha0 hw0
  refine ⟨(a * w)⁻¹, inv_ne_zero hd, fun x hx => hγ ?_⟩
  have h1 : valuation k ((a * w)⁻¹ * x) ≤ 1 := hx
  have h2 : valuation k x = valuation k (a * w) * valuation k ((a * w)⁻¹ * x) := by
    rw [← map_mul, mul_inv_cancel_left₀ hd]
  show valuation k x < γ
  calc valuation k x = valuation k (a * w) * valuation k ((a * w)⁻¹ * x) := h2
    _ ≤ valuation k (a * w) * 1 := mul_le_mul_right h1 _
    _ = γ * valuation k w := by rw [mul_one, map_mul, ha]
    _ < γ * 1 := mul_lt_mul_of_pos_left hw1 (zero_lt_iff.mpr γ.ne_zero)
    _ = γ := mul_one _

theorem exists_Lc_subset (t : ℕ) {W : Set (Fin t → k)} (hW : W ∈ 𝓝 (0 : Fin t → k)) :
    ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, o.toAdd ∈ W := by
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, s, hs, hsub⟩ := hW
  have hU : (⋂ j, s j) ∈ 𝓝 (0 : k) := Filter.iInter_mem.2 hs
  obtain ⟨c, hc, h⟩ := exists_inv_integer_subset hU
  exact ⟨c, hc, fun o ho => hsub fun j _ => Set.mem_iInter.1 (h _ (ho j)) j⟩

theorem exists_Lc_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v := by
  intro k _ _ _ _ t Z _ _ φ hl hc
  letI uG : UniformSpace (Fin t → k) := IsTopologicalAddGroup.rightUniformSpace _
  haveI : IsUniformAddGroup (Fin t → k) := isUniformAddGroup_of_addCommGroup
  letI uZ : UniformSpace Z := ⊥
  have huc : UniformContinuous φ := hc.uniformContinuous_of_continuous hl.continuous
  have hmem : {p : (Fin t → k) × (Fin t → k) | φ p.1 = φ p.2} ∈ 𝓤 (Fin t → k) := by
    have h0 : {q : Z × Z | q.1 = q.2} ∈ 𝓤 Z := by
      show _ ∈ 𝓤[(⊥ : UniformSpace Z)]
      rw [bot_uniformity]
      exact Filter.mem_principal_self _
    exact huc h0
  rw [uniformity_eq_comap_nhds_zero, Filter.mem_comap] at hmem
  obtain ⟨W, hW, hsub⟩ := hmem
  obtain ⟨c, hc0, h⟩ := exists_Lc_subset t hW
  refine ⟨c, hc0, fun o ho v => ?_⟩
  have hv : (v, v + o.toAdd) ∈ (fun x : (Fin t → k) × (Fin t → k) => x.2 - x.1) ⁻¹' W := by
    show v + o.toAdd - v ∈ W
    rw [add_sub_cancel_left]
    exact h o ho
  exact (hsub hv).symm

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionUnipotentAction
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU

variable {k : Type} [Field k]

theorem extTensor_fst_one {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (a : G) :
    extTensor ρ σ (a, 1) = LinearMap.rTensor W (ρ a) := by
  apply TensorProduct.ext'
  intro v w
  rw [extTensor_tmul, LinearMap.rTensor_tmul]
  show ρ a v ⊗ₜ[ℂ] σ 1 w = _
  rw [map_one, Module.End.one_apply]

theorem uM_comm (n : ℕ) (a b : Fin n → k) : uM k n a * uM k n b = uM k n b * uM k n a := by
  rw [← uM_add, ← uM_add]
  exact congrArg _ (add_comm a b)

theorem midV_add (i t : ℕ) (a b : Fin t → k) : midV k i t (a + b) = midV k i t a + midV k i t b := by
  funext j
  induction j using Fin.addCases <;> simp [midV]

theorem col_eq (i t : ℕ) (a : Fin (i + t) → k) : a = topV k i t (topP i t a) + midV k i t (middlePart i t a) := by
  rw [topV_add_midV]
  funext j
  induction j using Fin.addCases <;> simp [topP, middlePart]

theorem point_mul_uM (i t : ℕ) (κ : GL (Fin (i + t)) k) (v : Fin t → k) (y : Fin (i + t) → k) :
    uM k (i + t) (midV k i t v) * levi k (i + t) κ * uM k (i + t) y =
      uM k (i + t) (topV k i t (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) *
        (uM k (i + t) (midV k i t (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) *
          levi k (i + t) κ) := by
  rw [mul_assoc, levi_mul_uM, ← mul_assoc, ← mul_assoc, midV_add, uM_add]
  congr 1
  conv_lhs => rw [col_eq i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y), uM_add]
  rw [← mul_assoc, uM_comm (i + t) (midV k i t v)]
  exact mul_assoc _ _ _

theorem cInd_point {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup U] [Module ℂ U]
    (H : Subgroup G) (ρ : Representation ℂ H U) (x : G) (f : cIndSpace H ρ) (p : G) :
    (cInd H ρ x f).1.1.1 p = f.1.1.1 (p * x) := rfl

theorem cInd_equi {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup U] [Module ℂ U]
    (H : Subgroup G) (ρ : Representation ℂ H U) (f : cIndSpace H ρ) (h : H) (p : G) :
    f.1.1.1 ((h : G) * p) = ρ h (f.1.1.1 p) := f.1.1.2 h p

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fibV_uM_of (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (κ : GL (Fin (i + t)) k) (v : Fin t → k)
    (h : uM k (i + t) (topV k i t (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) ∈ HPG k i t)
    (hp : pgProj k i t ⟨_, h⟩ = (uM k i (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)), 1)) :
    fibV (prodPG τ σ (uM k (i + t) y) f) κ v =
      topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)))
        (fibV f κ (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) := by
  have e1 : fibV (prodPG τ σ (uM k (i + t) y) f) κ v =
      f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) κ * uM k (i + t) y) :=
    cInd_point (HPG k i t) (hRep τ σ) (uM k (i + t) y) f _
  have e2 := congrArg f.1.1.1 (point_mul_uM i t κ v y)
  have e3 := cInd_equi (HPG k i t) (hRep τ σ) f ⟨_, h⟩ (uM k (i + t) (midV k i t (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) *
    levi k (i + t) κ)
  have e4 : hRep τ σ ⟨_, h⟩ = topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) :=
    (congrArg (extTensor τ σ) hp).trans (extTensor_fst_one τ σ _)
  exact e1.trans (e2.trans (e3.trans (LinearMap.congr_fun e4 _)))
end

theorem fibV_uM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (κ : GL (Fin (i + t)) k) (v : Fin t → k), fibV (prodPG τ σ (uM k (i + t) y) f) κ v = topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) (fibV f κ (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ f y κ v
  exact Exists.elim (_root_.GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main k i t (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)))
    (fun h hp => fibV_uM_of τ σ f y κ v h hp)

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesLevi
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibUnip

theorem map_smInt_translate {X Z Z' : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [MeasurableSpace X] [BorelSpace X] [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z']
    (μ : MeasureTheory.Measure X) [μ.IsAddHaarMeasure]
    (L : Z →ₗ[ℂ] Z') (T : Z →ₗ[ℂ] Z) (hT : ∀ z, L (T z) = L z) (φ : X → Z) (m : X)
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    L (smInt μ (fun v => T (φ (v + m)))) = L (smInt μ φ) := by
  obtain ⟨_, h2, h3, _⟩ := SmIntEl.smInt_properties (X := X) (W := Z) (W' := Z) μ
  have hl' : IsLocallyConstant (φ ∘ fun v => v + m) := hl.comp_continuous ((continuous_id.add continuous_const))
  have hc' : HasCompactSupport (φ ∘ fun v => v + m) :=
    hc.comp_homeomorph (Homeomorph.addRight m)
  have e1 : smInt μ (T ∘ (φ ∘ fun v => v + m)) = T (smInt μ (φ ∘ fun v => v + m)) := h2 T _ hl' hc'
  have e2 : smInt μ (φ ∘ fun v => v + m) = smInt μ φ :=
    h3 (fun v => v + m) φ (MeasureTheory.measurePreserving_add_right μ m) hl
  calc L (smInt μ (fun v => T (φ (v + m)))) = L (T (smInt μ (φ ∘ fun v => v + m))) :=
        congrArg L e1
    _ = L (smInt μ (φ ∘ fun v => v + m)) := hT _
    _ = L (smInt μ φ) := congrArg L e2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem midV_add (i t : ℕ) (v m : Fin t → k) :
    midV k i t (v + m) = midV k i t v + midV k i t m := by
  funext j
  induction j using Fin.addCases <;> simp [midV]

theorem mul_uM_eq (i t : ℕ) (g : GL (Fin (i + t)) k) (y : Fin (i + t) → k) (x : Fin i → k) (m v : Fin t → k)
    (hy : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    uM k (i + t) (midV k i t v) * levi k (i + t) g * uM k (i + t) y =
      uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g) := by
  have e : midV k i t v + (topV k i t x + midV k i t m) = topV k i t x + midV k i t (v + m) := by
    rw [midV_add]; abel
  rw [mul_assoc, levi_mul_uM, hy, ← mul_assoc, ← uM_add, e, uM_add, mul_assoc]

variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem clT_extTensor (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (x : Fin i → k) (z : V ⊗[ℂ] W) :
    clT τ W (extTensor τ σ (uM k i x, 1) z) = clT τ W z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | tmul a b =>
    have hq : (twKer τ (MirUin k i) 1).mkQ (τ (uM k i x) a) = (twKer τ (MirUin k i) 1).mkQ a := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨_, uM_mem k i x⟩, a, ?_⟩)
      simp
    rw [extTensor_tmul]
    simp only [clT, LinearMap.rTensor_tmul, map_one, Module.End.one_apply]
    exact congrArg (· ⊗ₜ[ℂ] b) hq


set_option maxHeartbeats 1000000 in
theorem fibV_prodPG (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) (y : Fin (i + t) → k)
    (x : Fin i → k) (m v : Fin t → k)
    (hy : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    fibV (prodPG τ σ (uM k (i + t) y) f) g v = extTensor τ σ (uM k i x, 1) (fibV f g (v + m)) := by
  refine Exists.elim (_root_.GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main k i t x) fun hmem hproj => ?_
  have e1 : fibV (prodPG τ σ (uM k (i + t) y) f) g v =
      f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) g * uM k (i + t) y) := rfl
  have e2 := f.1.1.2 ⟨_, hmem⟩ (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g)
  calc fibV (prodPG τ σ (uM k (i + t) y) f) g v
      = f.1.1.1 (uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g)) :=
        e1.trans (congrArg f.1.1.1 (mul_uM_eq i t g y x m v hy))
    _ = extTensor τ σ (pgProj k i t ⟨_, hmem⟩) (fibV f g (v + m)) := e2
    _ = extTensor τ σ (uM k i x, 1) (fibV f g (v + m)) :=
        congrArg (fun a => extTensor τ σ a (fibV f g (v + m))) hproj

theorem fibInt_col (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (g : GL (Fin (i + t)) k)
    (x : Fin i → k) (m : Fin t → k)
    (hxm : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    fibInt μ (prodPG τ σ (uM k (i + t) y) f) g = fibInt μ f g := by
  have hlc := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main k i t τ σ hτ hσ f g
  have hfun : fibV (prodPG τ σ (uM k (i + t) y) f) g =
      fun v => (extTensor τ σ (uM k i x, 1)) (fibV f g (v + m)) :=
    funext fun v => fibV_prodPG τ σ f g y x m v hxm
  have h1 : clT τ W (smInt μ (fibV (prodPG τ σ (uM k (i + t) y) f) g)) =
      clT τ W (smInt μ fun v => (extTensor τ σ (uM k i x, 1)) (fibV f g (v + m))) :=
    congrArg (fun φ => clT τ W (smInt μ φ)) hfun
  exact h1.trans (map_smInt_translate μ (clT τ W) (extTensor τ σ (uM k i x, 1))
          (clT_extTensor τ σ x) (fibV f g) m hlc.1 hlc.2)


set_option maxHeartbeats 1000000 in
theorem fibInt_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (u : Mir k (i + t)), u ∈ MirUin k (i + t) → ∀ g : GL (Fin (i + t)) k, fibInt μ (prodPG τ σ u f) g = fibInt μ f g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f u hu g
  refine Exists.elim (exists_uM_of_mem k (i + t) hu) fun y hy => ?_
  refine Exists.elim (exists_top_mid k i t ((g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)) fun x hx => ?_
  refine Exists.elim hx fun m hxm => ?_
  exact (congrArg (fun u' => fibInt μ (prodPG τ σ u' f) g) hy).trans
    (fibInt_col τ σ hτ hσ μ f y g x m hxm)

end GlobalTheory.CompanionTheory.BZPsiPG.FibUnip

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSkewMatricesConjScalingStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_skew_matrices_conj_scaling : ∀ (D : D7) (r : ℕ) (κ : Measure (skewA D r)), κ.IsAddHaarMeasure → ∀ a : GL (Fin r) (AE D), κ.map (skewConj a.1) = ((absA D (Matrix.GeneralLinearGroup.det a) ^ r)⁻¹ : ℝ≥0) • κ := by
  first | exact @GlobalTheory.CompanionTheory.SkewMod.map_skewConj | exact GlobalTheory.CompanionTheory.SkewMod.map_skewConj | (intros; apply GlobalTheory.CompanionTheory.SkewMod.map_skewConj <;> assumption)
end

