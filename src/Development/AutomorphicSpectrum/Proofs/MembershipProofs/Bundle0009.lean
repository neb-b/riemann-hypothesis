module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SeesawThetaDualPair
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivariance
public import GroundTheory.GlobalFields.Adele.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumTensorProduct
section
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ThetaMember

section General

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β : Type} [Fintype β] [DecidableEq β]

theorem isHerm_dbl {J : Matrix β β E} (h : IsHerm c J) : IsHerm c (dbl J) := by
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) <;> simp [dbl, h.1]
  · rw [dbl, det_fromBlocks_zero₂₁, det_neg]
    exact h.2.mul ((isUnit_one.neg.pow _).mul h.2)

theorem exists_dbl_elem {J : Matrix β β E} (g : UG c J) : ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
  refine ⟨⟨⟨fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1,
    fromBlocks (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [fromBlocks_multiply, Units.mul_inv]; simp
  · rw [fromBlocks_multiply, Units.inv_mul]; simp
  · change (fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
      (fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl J
    rw [fromBlocks_map, fromBlocks_transpose, dbl, fromBlocks_multiply, fromBlocks_multiply,
      Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_zero _ (map_zero c)]
    simp [hg]

end General

def dblCoord {F : Type} [Field F] {E : Type} [AddCommGroup E] [Module F E] {α β κ : Type}
    (d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F)) :
    Matrix α (β ⊕ β) E ≃ₗ[F] (κ ⊕ κ → F) × (κ ⊕ κ → F) where
  toFun x := (Sum.elim (d₀ x.toCols₁).1 (d₀ x.toCols₂).1, Sum.elim (d₀ x.toCols₁).2 (-(d₀ x.toCols₂).2))
  invFun p := fromCols (d₀.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl)) (d₀.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
  map_add' x y := by
    have h1 : (x + y).toCols₁ = x.toCols₁ + y.toCols₁ := rfl
    have h2 : (x + y).toCols₂ = x.toCols₂ + y.toCols₂ := rfl
    rw [h1, h2, map_add (f := _), map_add (f := _)]
    ext (i | i) <;> simp [add_comm]
  map_smul' a x := by
    have h1 : (a • x).toCols₁ = a • x.toCols₁ := rfl
    have h2 : (a • x).toCols₂ = a • x.toCols₂ := rfl
    rw [h1, h2, map_smul, map_smul]
    ext (i | i) <;> simp
  left_inv x := by
    simp
  right_inv p := by
    simp only [toCols₁_fromCols, toCols₂_fromCols, LinearEquiv.apply_symm_apply]
    ext (i | i) <;> simp

theorem split_of_eq (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype κ] (JA : Matrix α α E) (JB : Matrix β β E) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (h1 : Continuous ψ) (h2 : ψ ≠ 1) (h3 : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1)
    (hq : IsQuad c ξ) (hA : IsHerm c JA) (hB : IsHerm c JB)
    (J' : Matrix β β (AdeleRing (𝓞 F) F ⊗[F] E)) (hJ : JB.map (fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) = J')
    (d : Darboux (symp (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) J') κ)
    (d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F))
    (hd : ∀ x, d.e (x.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) =
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).2 i)))
    (χ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle) (ν : Type) [Fintype ν] [DecidableEq ν] (Cy : Matrix β ν E)
    (C' : Matrix β ν (AdeleRing (𝓞 F) F ⊗[F] E)) (hC : Cy.map (fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) = C')
    (om : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) J' →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (hχ : ∀ (z : E) (u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), (u : AdeleRing (𝓞 F) F ⊗[F] E) = (1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z → χ u = 1)
    (hL : IsLagr c JB Cy) (hS : IsSplitting (adeleClass F) ψ d (actB (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c)) om)
    (hR : SiegelRule (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (adeleClass F) ψ ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) J' d χ C' om)
    (g : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) J')
    (hg : ∃ γ : Matrix β β E, ((g : GL β (AdeleRing (𝓞 F) F ⊗[F] E)) : Matrix β β (AdeleRing (𝓞 F) F ⊗[F] E)) = γ.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) :
    ∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ := by
  subst hJ hC
  exact _root_.GlobalTheory.CompanionTheory.ThetaSplit.theta_split F E c ξ α β κ JA JB ψ h1 h2 h3 hq hA hB d d₀ hd χ ν Cy om hχ hL hS hR g hg

theorem theta_om_rational : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (JA : Matrix α α E) (JB : Matrix β β E) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → IsQuad c ξ → IsHerm c JA → IsHerm c JB → ∀ (d : Darboux (symp (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E))) κ) (d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F)), (∀ x, d.e (x.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) = (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).2 i))) → ∀ (χ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle) (om : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)), (∀ (z : E) (u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), (u : AdeleRing (𝓞 F) F ⊗[F] E) = (1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z → χ u = 1) → IsWeilB (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (adeleClass F) ψ ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) d χ om → ∀ g : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)), (∃ γ : Matrix β β E, ((g : GL β (AdeleRing (𝓞 F) F ⊗[F] E)) : Matrix β β (AdeleRing (𝓞 F) F ⊗[F] E)) = γ.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) → ∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ := by
  intro F _ _ _ _ E _ _ c ξ α β κ _ _ _ _ _ JA JB ψ h1 h2 h3 hq hA hB d d₀ hd χ om hχ hW g hg Φ hΦ
  obtain ⟨hS, dd, omd, hdd, hSd, hRd, hbox⟩ := hW
  obtain ⟨γ, hγ⟩ := hg
  obtain ⟨gd, hgd⟩ := exists_dbl_elem g
  obtain ⟨-, -, Φ₀, hΦ₀, hne⟩ := GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have key := split_of_eq F E c ξ α (β ⊕ β) (κ ⊕ κ) JA (dbl JB) ψ h1 h2 h3 hq hA (isHerm_dbl hB) _ ?_ dd
    (dblCoord d₀) ?_ χ β (diagCols β) _ ?_ omd hχ (isLagr_diagCols c JB) hSd hRd gd ⟨fromBlocks γ 0 0 1, ?_⟩
    (boxFun Φ Φ₀) (_root_.GlobalTheory.CompanionTheory.ThetaBox.theta_box F κ κ Φ hΦ Φ₀ hΦ₀).1
  · rw [hbox g gd hgd Φ hΦ Φ₀ hΦ₀, (_root_.GlobalTheory.CompanionTheory.ThetaBox.theta_box F κ κ _ (hS.pres g Φ hΦ) Φ₀ hΦ₀).2,
      (_root_.GlobalTheory.CompanionTheory.ThetaBox.theta_box F κ κ Φ hΦ Φ₀ hΦ₀).2] at key
    exact mul_right_cancel₀ hne key
  · ext (i | i) (j | j) <;> simp [dbl, TensorProduct.tmul_neg]
  · intro x
    rw [← fromCols_toCols x, fromCols_map, hdd, hd, hd]
    ext (i | i) <;> simp [dblCoord]
  · ext (i | i) j <;> by_cases h : i = j <;> simp [diagCols, h, Matrix.one_apply, Algebra.TensorProduct.one_def]
  · rw [hgd, hγ]
    ext (i | i) (j | j)
    · simp
    · simp
    · simp
    · by_cases h : i = j <;> simp [h, Matrix.one_apply, Algebra.TensorProduct.one_def]

end GlobalTheory.CompanionTheory.ThetaMember
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationSplittingsDiffer
section
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.SplitRatio

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]


open GroundTheory.Global in
theorem exists_schA_compact : ∃ Φ ∈ schA F κ, Continuous Φ ∧ HasCompactSupport Φ ∧ Φ 0 ≠ 0 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := default
  have hb : HasCompactSupport fun v => (b v : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hb' : ContDiff ℝ (⊤ : ℕ∞) fun v => (b v : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) := hb.toSchwartzMap hb'
  have hf : ∀ v, f v = (b v : ℂ) := fun _ => rfl
  set O := Set.univ.pi fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hO
  set g := O.indicator fun _ => (1 : ℂ) with hgd
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have hc : IsCompact O := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
    have ho : IsOpen O := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
    have hcl : IsClosed O := isClosed_set_pi fun _ _ =>
      AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup GroundTheory.Global.isOpen_integralFiniteAdeles
    refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ O
    · exact ⟨_, ho, hx, fun y hy => by rw [hgd, Set.indicator_of_mem hx, Set.indicator_of_mem hy]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [hgd, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  refine ⟨pureA F f g, Submodule.subset_span ⟨f, _, hg, rfl⟩, ?_, ?_, ?_⟩
  · refine (f.continuous.comp (continuous_pi fun i => ?_)).mul (hg.1.continuous.comp (continuous_pi fun i => ?_))
    · exact (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_snd.comp (continuous_apply i)
  · let m : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
      fun p i => ((GroundTheory.Global.homeomorphMixedSpace F).symm (p.1 i), p.2 i)
    have hm : Continuous m := continuous_pi fun i =>
      ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply i).comp continuous_fst)).prodMk
        ((continuous_apply i).comp continuous_snd)
    refine HasCompactSupport.intro ((hb.isCompact.prod hg.2.isCompact).image hm) fun x hx => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
    refine hx ⟨(_, _), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, funext fun i => ?_⟩
    exact Prod.ext ((GroundTheory.Global.homeomorphMixedSpace F).symm_apply_apply (x i).1) rfl
  · have h0 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ O := fun i _ => Subring.zero_mem _
    have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 :=
      funext fun i => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    rw [pureA, h1, hf, hgd, Set.indicator_of_mem h0,
      b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    simp

end GlobalTheory.CompanionTheory.SplitRatio
end

