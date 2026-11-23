module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CorrESymmCoe
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0050
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLaws
section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgTransfer

theorem transfer : SecLaw → WallLaw → Transfer := by
  intro hSec hWall G _ _ _ _ _ W _ _ _ K ρ hK hρ G' _ _ _ _ _ Γ Q S P₁ P₂ Γ' K' S' P₁' P₂' π ι c₀ c c'
    η₁ η₂ β ξ η₁' η₂' β' ξ' N hK' hL hS hP₁ hP₂ hS' hR₁ hR₂ hη₁ hη₂ hβ hp₁ hp₂ hpβ hpξ
  have hcont := resRep_cont hL hρ
  have c1 : c' 1 = 1 := isCh_one hR₁.ch
  have corr : ∀ {P : Subgroup G} {P' : Subgroup G'}, IsPull Q P P' π c₀ c c' →
      Corr ρ (secSp K P c ρ) (secSp K' P' c' (resRep hL ρ)) :=
    fun h w => mem_secSp_iff hL h c1 ρ w
  have lawG : ∀ {P : Subgroup G} {P' : Subgroup G'}, IsPull Q P P' π c₀ c c' →
      IsPar Γ' K' P' c' → Law K P c ρ :=
    fun h hp => (hSec G W K ρ hK hρ (Γ ⊓ Q) _ c (isPar_pull hL h hp)).1
  have lawG' : ∀ {P' : Subgroup G'}, IsPar Γ' K' P' c' → Law K' P' c' (resRep hL ρ) :=
    fun hp => (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hp).1
  obtain ⟨M₁, bd₁⟩ := (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hR₁).2.2
  obtain ⟨M₂, bd₂⟩ := (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hR₂).2.2
  have equi : ∀ {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} {R : ℝ} {D : ℂ → ℂ}
      {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
      {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)},
      Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H' →
      ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w) :=
    fun hw => (hWall G' _ K' (resRep hL ρ) hK' hcont Γ' P₁' P₂' c' η₁' η₂' β' _ _ _ _ _ hR₁ hR₂
      hη₁ hη₂ hβ hw).2.1
  have key : ∀ {L : Submodule ℂ W} {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} (hLL : Corr ρ L L')
      {R : ℝ} {D : ℂ → ℂ} {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
      {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)},
      Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H' →
      Wall (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ L R D (fun z => cj (corrE hLL) (corrE (corr hP₂)) (Op' z))
        (hOf hL ρ (corrE hLL) H') :=
    fun hLL _ _ _ _ hw => wall_pull hK hL hρ hP₁ hP₂ hR₁ hR₂ hη₁ hη₂ hβ hp₁ hp₂ hpβ (lawG hP₁ hR₁)
      (lawG hP₂ hR₂) (lawG' hR₁) (lawG' hR₂) bd₁ bd₂ hLL (corr hP₁) (corr hP₂) hw (equi hw)
  have hCS := corr hS
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨R, D, Op', H', hw⟩ := h _ (resRep hL ρ) hcont
    exact ⟨R, D, _, _, key (corr hP₁) hw⟩
  · obtain ⟨R, D, Op', H', hw, ⟨a, ha, hH0⟩, O', hO, hOp⟩ := h _ (resRep hL ρ) hcont
    refine ⟨R, D, _, _, key hCS hw, ⟨a, ha, fun g w => ?_⟩,
      fun z => cj (corrE hCS) (corrE (corr hP₂)) (O' z),
      leftGood_comp (cj (corrE hCS) (corrE (corr hP₂))) hO, fun z hz => ?_⟩
    · obtain ⟨q, k, rfl⟩ := exists_qk hL g
      rw [hOf_eq hL ρ _ (equi hw), hH0, map_smul]
      have := sec_pull hL hS hS'.iwa (lawG hS hS') (lawG' hS') (corrE hCS w).2 w.2 q k
      exact congrArg (fun u => a • u) this.symm
    · show cj (corrE hCS) (corrE (corr hP₂)) (Op' z) = z • cj (corrE hCS) (corrE (corr hP₂)) (O' z)
      rw [hOp z hz, map_smul]
  · obtain ⟨R, D, Op', H', hw, hd, T', hT⟩ := h _ (resRep hL ρ) hcont
    refine ⟨R, D, _, _, key (corr hP₁) hw, hd, cj (corrE (corr hP₁)) (corrE hCS) T', fun g w => ?_⟩
    obtain ⟨q, k, rfl⟩ := exists_qk hL g
    rw [hOf_eq hL ρ _ (equi hw), hT, map_smul, hpξ q k k.2]
    have := sec_pull hL hS hS'.iwa (lawG hS hS') (lawG' hS') (T' (corrE (corr hP₁) w)).2
      (cj (corrE (corr hP₁)) (corrE hCS) T' w).2 q k
    exact congrArg (fun u => Complex.exp (ξ' (π q)) • u) this.symm

end GlobalTheory.CompanionTheory.RgTransfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLaw
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisTwist

open PositivityTheory.RgEis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K : Subgroup G} {c₀ : G → ℂ}

lemma ch_mul (h : IsCh Γ ⊤ c₀) (a b : G) : c₀ (a * b) = c₀ a * c₀ b :=
  h.mul a (Subgroup.mem_top a) b (Subgroup.mem_top b)

lemma ch_one (h : IsCh Γ ⊤ c₀) : c₀ 1 = 1 :=
  h.rat 1 (one_mem _) (Subgroup.mem_top 1)

lemma ch_rat_mul (h : IsCh Γ ⊤ c₀) {γ : G} (hγ : γ ∈ Γ) (g : G) : c₀ (γ * g) = c₀ g := by
  rw [ch_mul h, h.rat γ hγ (Subgroup.mem_top γ), one_mul]

lemma ch_norm (h : IsCh Γ ⊤ c₀) (g : G) : ‖c₀ g‖ = 1 :=
  h.norm g (Subgroup.mem_top g)

lemma ch_cont (h : IsCh Γ ⊤ c₀) : Continuous c₀ := by
  have h' := h.cont
  rw [Subgroup.coe_top] at h'
  exact continuousOn_univ.mp h'

def twRep (h : IsCh Γ ⊤ c₀) (K : Subgroup G) (ρ : K →* (W →L[ℂ] W)) : K →* (W →L[ℂ] W) where
  toFun r := c₀ r • ρ r
  map_one' := by simp [ch_one h]
  map_mul' a b := by
    ext w
    simp [ch_mul h, smul_smul, mul_comm]

lemma twRep_apply (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (r : K) :
    twRep h K ρ r = c₀ r • ρ r := rfl

lemma twRep_cont (h : IsCh Γ ⊤ c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) :
    Continuous (twRep h K ρ) :=
  ((ch_cont h).comp continuous_subtype_val).smul hρ

lemma secSp_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) :
    secSp K P (c * c₀) ρ = secSp K P c (twRep h K ρ) := by
  ext w
  have key : ∀ r : K, (c * c₀) (r : G) • ρ r w = c (r : G) • twRep h K ρ r w := fun r => by
    rw [twRep_apply, smul_apply, smul_smul, Pi.mul_apply]
  change (∀ r : K, (r : G) ∈ P → (c * c₀) (r : G) • ρ r w = w) ↔
    ∀ r : K, (r : G) ∈ P → c (r : G) • twRep h K ρ r w = w
  simp only [key]

lemma sec_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (g : G) :
    sec K P (c * c₀) ρ g = c₀ g • sec K P c (twRep h K ρ) g := by
  unfold sec
  by_cases hk : ∃ k : K, g * (k : G)⁻¹ ∈ P
  · rw [dite_eq_left hk, dite_eq_left hk, twRep_apply, Pi.mul_apply, Subgroup.coe_inv, ch_mul h g, smul_smul, smul_smul]
    congr 1
    ring
  · rw [dite_eq_right hk, dite_eq_right hk, smul_zero]

lemma eis_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (Λ : G → ℂ)
    (g : G) (w : W) :
    eis Γ K P (c * c₀) ρ Λ g w = c₀ g • eis Γ K P c (twRep h K ρ) Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [sec_twist h, smul_apply, ch_rat_mul h hq, smul_comm]

def castL {A B : Submodule ℂ W} (e : A = B) : A →L[ℂ] B :=
  (ContinuousLinearEquiv.ofEq A B e).toContinuousLinearMap

lemma leftGood_cast {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {A B : Submodule ℂ W} (e : A = B)
    {Op : ℂ → (X →L[ℂ] A)} {a : ℝ} (hO : LeftGood Op a) :
    LeftGood (fun z => (castL e).comp (Op z)) a := by
  subst e
  have hid : (fun z => (castL (rfl : A = A)).comp (Op z)) = Op := by
    funext z
    ext x
    rfl
  rwa [hid]

lemma wall_twist (h : IsCh Γ ⊤ c₀) {P P' : Subgroup G} {c : G → ℂ} {η η' β : G → ℝ}
    {ρ : K →* (W →L[ℂ] W)} {L : Submodule ℂ W} {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (L →L[ℂ] secSp K P' c (twRep h K ρ))} {H : ℂ → G → (L →L[ℂ] W)}
    (hw : Wall Γ K P P' c η η' β (twRep h K ρ) L R D Op H) :
    Wall Γ K P P' (c * c₀) η η' β ρ L R D
      (fun z => (castL (secSp_twist h ρ P' c).symm).comp (Op z)) (fun z g => c₀ g • H z g) := by
  refine
    { le := ?_
      pos := hw.pos
      convR := hw.convR
      convL := hw.convL
      dEnt := hw.dEnt
      dNe := hw.dNe
      op := leftGood_cast _ hw.op
      hol := fun g => (hw.hol g).const_smul (c₀ g)
      cont := ((ch_cont h).comp continuous_snd).smul hw.cont
      bdd := ?_
      eqR := ?_
      eqL := ?_ }
  · rw [secSp_twist h ρ P c]
    exact hw.le
  · intro b a g
    obtain ⟨U, hU, M, hM⟩ := hw.bdd b a g
    refine ⟨U, hU, M, fun z h1 h2 g' hg' => ?_⟩
    rw [norm_smul, ch_norm h, one_mul]
    exact hM z h1 h2 g' hg'
  · intro z hz g w
    rw [smul_apply, hw.eqR z hz g w, eis_twist h, smul_comm]
  · intro z hz g w
    rw [smul_apply, hw.eqL z hz g w, eis_twist h]
    rfl

theorem twist : SecLaw → Twist := by
  intro _ G _ _ _ _ _ Γ K S P P' c c₀ η η' β ξ N _ h _ _ _
  refine ⟨fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_⟩
  · obtain ⟨R, D, Op, H, hw⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasWall
    rw [secSp_twist h ρ P c]
    exact ⟨R, D, _, _, wall_twist h hw⟩
  · obtain ⟨R, D, Op, H, hw, ⟨a, ha0, ha⟩, O, hO, hOp⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasFirst
    rw [secSp_twist h ρ S c]
    refine ⟨R, D, _, _, wall_twist h hw, ⟨a, ha0, fun g w => ?_⟩,
      fun z => (castL (secSp_twist h ρ P' c).symm).comp (O z), leftGood_cast _ hO, fun z hz => ?_⟩
    · rw [smul_apply, ha g w, sec_twist h, smul_apply, smul_comm]
    · rw [hOp z hz, ContinuousLinearMap.comp_smul]
  · obtain ⟨R, D, Op, H, hw, hd, T, hT⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasLast
    rw [secSp_twist h ρ P c]
    refine ⟨R, D, _, _, wall_twist h hw, hd,
      (castL (secSp_twist h ρ S c).symm).comp T, fun g w => ?_⟩
    rw [smul_apply, hT g w, sec_twist h, smul_apply, smul_comm]
    rfl

end GlobalTheory.CompanionTheory.RgEisTwist
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetExactSmooth
section
open GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.PRep.TwExact

theorem twMap_range_eq_ker : ∀ {G V₁ V₂ V₃ : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    (ρ₃ : Representation ℂ G V₃), IsSmooth ρ₁ → IsSmooth ρ₂ → IsSmooth ρ₃ →
    ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) →
    (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧
      IsCompact (L : Set G)) →
    ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v))
      (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v)), LinearMap.range f = LinearMap.ker g →
    LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg) := by
  intro G V₁ V₂ V₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ h₁ h₂ h₃ N θ hθ hN f g hf hg hfg
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer ρ₁ N θ) x
    rw [LinearMap.mem_ker]
    have hv : g (f v) = 0 := by
      have h0 : f v ∈ LinearMap.ker g := hfg ▸ LinearMap.mem_range_self f v
      exact LinearMap.mem_ker.mp h0
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, hv, Submodule.Quotient.mk_zero]
  · intro x hx
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer ρ₂ N θ) x
    rw [LinearMap.mem_ker] at hx
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    have hKinv : ∀ x : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (ρ₂ x) := by
      intro x u hu
      rw [Submodule.mem_comap, LinearMap.mem_ker, hg, LinearMap.mem_ker.mp hu, map_zero]
    let ρq : Representation ℂ G (V₂ ⧸ LinearMap.ker g) :=
      { toFun := fun x => (LinearMap.ker g).mapQ (LinearMap.ker g) (ρ₂ x) (hKinv x)
        map_one' := by
          ext u
          simp
        map_mul' := by
          intro x y
          ext u
          simp [Module.End.mul_apply] }
    have hq : GlobalTheory.PRep.IsSmooth ρq := by
      intro u
      obtain ⟨w0, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      rw [isOpen_iff_forall_mem_open]
      intro x0 hx0
      refine ⟨(fun y => x0 * y) '' {y | ρ₂ y w0 = w0}, ?_, isOpenMap_mul_left x0 _ (h₂ w0),
        ⟨1, by simp, by simp⟩⟩
      rintro _ ⟨y, hy, rfl⟩
      rw [Set.mem_ofPred_eq] at hy hx0 ⊢
      have e1 : ρq y (Submodule.Quotient.mk w0) = Submodule.Quotient.mk (ρ₂ y w0) := rfl
      rw [map_mul, Module.End.mul_apply, e1, hy, hx0]
    let gb : (V₂ ⧸ LinearMap.ker g) →ₗ[ℂ] V₃ := (LinearMap.ker g).liftQ g le_rfl
    have hgb_inj : Function.Injective gb := by
      intro a b hab
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      have hab' : g a = g b := hab
      rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, hab', sub_self]
    have hgb_eq : ∀ (x : G) (u : V₂ ⧸ LinearMap.ker g), gb (ρq x u) = ρ₃ x (gb u) := by
      intro x u
      obtain ⟨w0, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      exact hg x w0
    have hmem : (Submodule.Quotient.mk w : V₂ ⧸ LinearMap.ker g) ∈ GlobalTheory.PRep.twKer ρq N θ :=
      GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect ρq ρ₃ hq h₃ N θ hθ hN gb hgb_inj hgb_eq _ hx
    rw [GlobalTheory.CompanionTheory.PRep.twKer_map_closed ρ₂ ρq N θ (LinearMap.ker g).mkQ
      (Submodule.mkQ_surjective _) (fun x v => rfl)] at hmem
    obtain ⟨w', hw', hw'eq⟩ := hmem
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq, ← hfg, LinearMap.mem_range] at hw'eq
    obtain ⟨v, hv⟩ := hw'eq
    rw [LinearMap.mem_range]
    refine ⟨Submodule.Quotient.mk (-v), ?_⟩
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, map_neg, hv]
    rw [Submodule.Quotient.eq]
    have e2 : -(w' - w) - w = -w' := by abel
    rw [e2]
    exact Submodule.neg_mem _ hw'

end GlobalTheory.CompanionTheory.PRep.TwExact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoUnif
section
open PositivityTheory.Rg.BcB.E1
open scoped Pointwise Topology

namespace GlobalTheory.CompanionTheory.TwoSidedUnif

theorem twoUnif : TwoUnif := by
  intro X φ ε hφ hε
  obtain ⟨hc, hs⟩ := hφ
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have hS : IsCompact (tsupport φ) := hs
  have hK : IsCompact (N⁻¹ * tsupport φ * N⁻¹) := (hNc.inv.mul hS).mul hNc.inv
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hf : Continuous fun q : (X.G × X.G) × X.G => ‖φ (q.1.1 * q.2 * q.1.2) - φ q.2‖ := by
    have : Continuous fun q : (X.G × X.G) × X.G => q.1.1 * q.2 * q.1.2 := by fun_prop
    exact ((hc.comp this).sub (hc.comp continuous_snd)).norm
  have hev : ∀ᶠ p : X.G × X.G in 𝓝 ((1 : X.G), (1 : X.G)), ∀ y ∈ N⁻¹ * tsupport φ * N⁻¹,
      ‖φ (p.1 * y * p.2) - φ y‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h0 : ‖φ ((((1 : X.G), (1 : X.G)), y).1.1 * (((1 : X.G), (1 : X.G)), y).2 *
        (((1 : X.G), (1 : X.G)), y).1.2) - φ (((1 : X.G), (1 : X.G)), y).2‖ < ε := by
      simpa using hε
    exact hf.continuousAt.eventually (Iio_mem_nhds h0)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hev
  refine ⟨U ∩ V ∩ N, Filter.inter_mem (Filter.inter_mem hU hV) hN1, ?_⟩
  rintro z ⟨⟨hzU, -⟩, hzN⟩ w ⟨⟨-, hwV⟩, hwN⟩ y
  by_cases hy : y ∈ N⁻¹ * tsupport φ * N⁻¹
  · exact (hUV (Set.mk_mem_prod hzU hwV) y hy).le
  · have hy0 : φ y = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hys => hy ?_
      refine Set.mem_mul.2 ⟨1 * y, Set.mem_mul.2 ⟨1, ?_, y, hys, rfl⟩, 1, ?_, by simp⟩
      · simpa using h1N
      · simpa using h1N
    have hzy0 : φ (z * y * w) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hys => hy ?_
      refine Set.mem_mul.2 ⟨z⁻¹ * (z * y * w), Set.mem_mul.2 ⟨z⁻¹, ?_, z * y * w, hys, rfl⟩, w⁻¹, ?_, by group⟩
      · exact Set.inv_mem_inv.2 hzN
      · exact Set.inv_mem_inv.2 hwN
    simpa [hy0, hzy0] using hε.le

end GlobalTheory.CompanionTheory.TwoSidedUnif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatement
section
noncomputable section

open Matrix MeasureTheory

namespace GlobalTheory.CompanionTheory.Jp.Unif

theorem integral_coset {X G : Type*} [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [Group G] (N : Subgroup G) [Finite (G ⧸ N)] (ρ : X →* G)
    (hρ : Function.Surjective ρ) (hN : MeasurableSet (ρ ⁻¹' (N : Set G))) (c : G ⧸ N → ℂ) :
    ∫ x, c (QuotientGroup.mk (ρ x)) ∂ν = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ u, c u := by
  classical
  letI := Fintype.ofFinite (G ⧸ N)
  have hS : ∀ u : G ⧸ N, ∃ y : X, {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} =
      (fun x => y * x) ⁻¹' (ρ ⁻¹' (N : Set G)) := by
    intro u
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, hy⟩ := hρ g⁻¹
    refine ⟨y, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, map_mul, hy]
    rw [eq_comm, QuotientGroup.eq]
  choose y hy using hS
  have hmeas : ∀ u : G ⧸ N, MeasurableSet {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} := by
    intro u
    rw [hy u]
    exact hN.preimage (measurable_const_mul (y u))
  have hmeasure : ∀ u : G ⧸ N,
      ν.real {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} = ν.real (ρ ⁻¹' (N : Set G)) := by
    intro u
    rw [hy u]
    show (ν _).toReal = (ν _).toReal
    rw [measure_preimage_mul]
  have hdecomp : (fun x => c (QuotientGroup.mk (ρ x))) = fun x =>
      ∑ u, Set.indicator {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} (fun _ => c u) x := by
    funext x
    rw [Finset.sum_eq_single (QuotientGroup.mk (ρ x) : G ⧸ N)]
    · exact (Set.indicator_of_mem (show x ∈ {x' : X | (QuotientGroup.mk (ρ x') : G ⧸ N) =
        QuotientGroup.mk (ρ x)} from rfl) (fun _ => c (QuotientGroup.mk (ρ x)))).symm
    · intro u _ hu
      exact Set.indicator_of_notMem (by intro h; exact hu (Eq.symm h)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [finsum_eq_sum_of_fintype, hdecomp, integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [integral_indicator_const _ (hmeas u), hmeasure u, Complex.real_smul]
  · intro u _
    exact (integrable_const (c u)).indicator (hmeas u)

theorem integral_level {X G : Type*} [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [Group G] (N : Subgroup G) [Finite (G ⧸ N)] (ρ : X →* G)
    (hρ : Function.Surjective ρ) (hN : MeasurableSet (ρ ⁻¹' (N : Set G))) (φ : G → ℂ)
    (hφ : ∀ κ, ∀ γ ∈ N, φ (κ * γ) = φ κ) :
    ∫ x, φ (ρ x) ∂ν = (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) := by
  classical
  letI := Fintype.ofFinite (G ⧸ N)
  have hone : ∫ _x, (1 : ℂ) ∂ν = 1 := by simp
  have hsum : ∑ᶠ _u : G ⧸ N, (1 : ℂ) = (Nat.card (G ⧸ N) : ℂ) := by
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
      nsmul_eq_mul, mul_one]
  have h1 : ∫ _x, (1 : ℂ) ∂ν = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ _u : G ⧸ N, (1 : ℂ) :=
    GlobalTheory.CompanionTheory.Jp.Unif.integral_coset ν N ρ hρ hN (fun _ => 1)
  rw [hone, hsum] at h1
  have hA : (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) = (Nat.card (G ⧸ N) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1.symm
  calc ∫ x, φ (ρ x) ∂ν = ∫ x, φ (Quotient.out (QuotientGroup.mk (ρ x) : G ⧸ N)) ∂ν := by
        congr 1
        funext x
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (ρ x)
        rw [hh, hφ _ _ h.2]
    _ = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) :=
        GlobalTheory.CompanionTheory.Jp.Unif.integral_coset ν N ρ hρ hN (fun u => φ (Quotient.out u))
    _ = (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) := by rw [hA]

theorem finite_quot_sq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Fintype (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) : Finite (O ⧸ Ideal.span {ϖ ^ 2}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have : Finite (O ⧸ IsLocalRing.maximalIdeal O) := Finite.of_fintype (IsLocalRing.ResidueField O)
  rw [← Ideal.span_singleton_pow, ← hm]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) 2

theorem finite_quotient_level_square_congruence {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) {ϖ : O} (hϖ : Irreducible ϖ) :
    Finite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) := by
  haveI := GlobalTheory.CompanionTheory.Jp.Unif.finite_quot_sq hϖ
  haveI : Finite (Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) :=
    inferInstanceAs (Finite (GlobalTheory.CompanionTheory.Jp.Ix n → GlobalTheory.CompanionTheory.Jp.Ix n → O ⧸ Ideal.span {ϖ ^ 2}))
  haveI : Finite (GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) :=
    Finite.of_injective (fun g : GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) =>
      (g : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})))
      (fun _ _ h => Units.ext h)
  exact Finite.of_injective _ (QuotientGroup.kerLift_injective
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) :
      GL (GlobalTheory.CompanionTheory.Jp.Ix n) O →* GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})))

theorem jpUnif : JpUnif := by
  intro O _ _ _ _ n ϖ hϖ X _ _ _ ν _ _ ρ hρ hN φ hφ
  haveI := finite_quotient_level_square_congruence n hϖ
  exact integral_level ν (Gam2 (n := n) ϖ) ρ hρ hN φ hφ

end GlobalTheory.CompanionTheory.Jp.Unif

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaSecondHolds
section
open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.UnitFL

theorem unit_fundamental_lemma_second : PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.Z2 := by
  intro hL2 hN4
  unfold PositivityTheory.Rg.Tf.Loc.Z2
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n _ _ _ _ μE μk _ _ _ _ γ μγ _ hnot _
  have hno : ∀ g : GL (Fin n) k, g⁻¹ * γ * g ∉ unitGL (n := Fin n) k := by
    intro g hg
    obtain ⟨c, -, -, hc⟩ := hN4 k E hun σ hgen n γ (hL2.1 k n γ ⟨g, hg⟩)
    exact hnot ⟨c, 1, by simpa using hc⟩
  have hzero : (fun g : GL (Fin n) k => unitFn (n := Fin n) k (g⁻¹ * γ * g)) = fun _ => 0 := by
    funext g
    exact Set.indicator_of_notMem (hno g) _
  unfold orbIntegral quotLIntegral
  rw [hzero]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.UnitFL
end

