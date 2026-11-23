module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelCharacterBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212
public import Formalism.LocalRingCardinality.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalGenusBound
section
set_option synthInstance.maxHeartbeats 400000

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.CovGminTop

section Abstract

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem norm_sum_le_of_gram {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    {ι : Type} (s : Finset ι) (f : ι → V) (σ : K →+* ℂ) : N σ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N σ (f i) := by
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, h⟩ := hG
  have e : ∀ x, N σ x = Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk σ) x := fun x => by
    rw [(h _).2]
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e]
    · rw [e]; exact (hc σ x).symm
  simp only [e]
  exact PI.Dv.Tr.normAt_sum_le' b X _ s f

theorem char_val {H : Type} [Group H] [Finite H] (χ : H →* Kˣ) (h : H) :
    IsIntegral ℤ ((χ h : Kˣ) : K) ∧ ∀ σ : K →+* ℂ, ‖σ ((χ h : Kˣ) : K)‖ = 1 := by
  have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 : ((χ h : Kˣ) : K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (h1 ▸ isIntegral_one), fun σ => ?_⟩
  have : ‖σ ((χ h : Kˣ) : K)‖ ^ Nat.card H = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_short_eigen {H : Type} [Group H] [Finite H] (st : H → V →ₗ[K] V)
    (hst : ∀ h h' x, st (h * h') x = st h' (st h x)) (χ : H →* Kˣ) (Λ : Submodule (𝓞 K) V) (hΛ : ∀ h, ∀ x ∈ Λ, st h x ∈ Λ)
    {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (hs : ∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) (hi : ∀ h σ x, N σ (st h x) = N σ x)
    (s : Set V) (hsΛ : s ⊆ Λ) (hsp : Submodule.span K s = ⊤) (B : ℝ) (hB : ∀ y ∈ s, ∀ σ, N σ y ≤ B) :
    ∃ s' : Set V, (∀ y ∈ s', (y ∈ Λ ∧ ∀ h, st h y = ((χ h : Kˣ) : K) • y) ∧ ∀ σ, N σ y ≤ Nat.card H * B) ∧
      ∀ x, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K s' := by
  classical
  letI := Fintype.ofFinite H
  refine ⟨_, ?_, GlobalTheory.eigenvector_mem_span_twistedTrace_image H K V st hst χ s hsp⟩
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨⟨Λ.sum_mem fun h _ => ?_, fun g => ?_⟩, fun σ => ?_⟩
  · rw [← map_inv]
    let a : 𝓞 K := ⟨_, (char_val χ h⁻¹).1⟩
    have := Λ.smul_mem a (hΛ h y (hsΛ hy))
    rwa [← algebraMap_smul K a] at this
  · beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight g) fun h => _ • _ • st h y]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, ← hst, smul_smul, Equiv.coe_mulRight, map_mul, mul_inv, ← Units.val_mul, mul_left_comm, mul_inv_cancel, mul_one]
  · refine (norm_sum_le_of_gram hG hc _ _ σ).trans ?_
    rw [Nat.card_eq_fintype_card, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun h _ => ?_
    rw [hs, hi, ← map_inv, (char_val χ h⁻¹).2, one_mul]
    exact hB y hy σ

end Abstract

section Point

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem half_lt_laOf (τ : Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)) (hk : (k : ℕ) < (dat p i).p) :
    (((p.κ i).n / 2 : ℕ) : ℤ) < laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k := by
  have h := GlobalTheory.HolRead.lastPos_wtA_of_kapIs D p.T p.κ p.fw.laws p.fw.kap i τ.1 τ.2
  have hm : (dat p i).mult τ.1 = (dat p i).p := by
    unfold Datum.mult
    exact if_pos τ.2
  rw [hm] at h
  have h2 : wtA (p.κ i) (τ.1, (dat p i).p - 1) ≤ wtA (p.κ i) (τ.1, k) := (dom_wtA (p.κ i)).1 τ.1 (show (k : ℕ) ≤ _ by omega)
  have h3 := h (by omega)
  unfold laOf weightOf
  rw [if_pos hk]
  beta_reduce
  omega

theorem one_le_kap (hp : 1 ≤ (dat p i).p) : 1 ≤ kap p i := by
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.two_le_m
    have := D.R.m_le_f
    omega
  have hne : Nonempty (Psi p.T.Q.H) := (Nat.card_pos_iff.1 (by rw [WtShape.card_psi p]; exact hf)).1
  obtain ⟨τ⟩ := hne
  have h := half_lt_laOf p i τ ⟨0, by omega⟩ hp
  have h1 : (1 : ℤ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by omega
  have h2 : (1 : ℝ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by exact_mod_cast h1
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact (h2.trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun k => |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem gminAt_of_gens (Y : Cov p i) (hpq : 1 ≤ (dat p i).p + (dat p i).q) (hA : Y.d.l₂.A.Coprime Y.d.l₂.M)
    (hC : KeepsCusp Y.U (Gk p i))
    (hk : ∀ (γ : LevelAut (dat p i) Y.d.l₂) (f g : Y.V (Gk p i)), (g : Rul Y.d.Xo₂ Y.d.c₂) = pull Y.d.Xo₂ Y.d.c₂ γ f →
      (f ∈ latW Y.U (Gk p i) → g ∈ latW Y.U (Gk p i)) ∧ ∀ σ, Y.nrm (Gk p i) σ g = Y.nrm (Gk p i) σ f)
    (hG : Y.GoodAt (Gk p i)) (S : Subgroup (LevelAut (dat p i) Y.d.l₂)) (χ : S →* (Y.d.c₂.F)ˣ)
    (hN : latDeep p i Y = chiLat S Y.U (Gk p i) χ) (s : Set (Y.V (Gk p i))) (hs : s ⊆ latW Y.U (Gk p i))
    (hsp : Submodule.span Y.d.c₂.F s = ⊤) (B PP : ℝ) (hB : ∀ y ∈ s, ∀ σ, Y.nrm (Gk p i) σ y ≤ Real.exp B)
    (hPP : Real.log (Nat.card S) + B ≤ PP * kap p i) : GminAt p i Y PP := by
  let st : S → Y.V (Gk p i) →ₗ[Y.d.c₂.F] Y.V (Gk p i) := fun h =>
    (pull Y.d.Xo₂ Y.d.c₂ (h : LevelAut (dat p i) Y.d.l₂)).toLinearMap.restrict (hC h)
  obtain ⟨s', h1, h2⟩ := exists_short_eigen st
    (fun h h' x => Subtype.ext ((isRightAct_pull (Xo := Y.d.Xo₂) (c := Y.d.c₂) hpq hA).2 h h' x)) χ (latW Y.U (Gk p i))
    (fun h x hx => (hk h x _ rfl).1 hx) hG.1
    (fun σ f => by rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ])
    (fun σ a x => petW_smul _ _ _ _ _ σ a _) (fun h σ x => (hk h x _ rfl).2 σ) s hs hsp _ hB
  refine ⟨s', fun y hy => ?_, fun y hy σ => ((h1 y hy).2 σ).trans ?_, fun x hx => h2 x fun h => Subtype.ext ?_⟩
  · rw [hN]
    exact (mem_chiLat S Y.U _).2 ⟨(h1 y hy).1.1, fun h => congrArg Subtype.val ((h1 y hy).1.2 h)⟩
  · have hc : (0 : ℝ) < Nat.card S := by exact_mod_cast Nat.card_pos
    rw [← Real.exp_log hc, ← Real.exp_add]
    exact Real.exp_le_exp.2 hPP
  · rw [hN] at hx
    exact ((mem_chiLat S Y.U _).1 hx).2 h

end Point

theorem num_step {C Z l k PP : ℝ} (hC : 0 ≤ C) (hl : C + 45 ≤ Z) (hk : 1 ≤ k) (hPP : Z ^ 12 ≤ PP) (h : l ≤ 45 * Z ^ 2) :
    l + C * Z ^ 2 * k ≤ PP * k := by
  have h1 : 1 ≤ Z := by linarith
  have h2 : Z ^ 3 ≤ Z ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have h3 : (C + 45) * Z ^ 2 ≤ Z ^ 3 := by
    rw [pow_succ' Z 2]; exact mul_le_mul_of_nonneg_right hl (by positivity)
  have h4 : (C + 45) * Z ^ 2 * k ≤ PP * k := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h5 : 45 * Z ^ 2 ≤ 45 * Z ^ 2 * k := le_mul_of_one_le_right (by positivity) hk
  linarith

end GlobalTheory.CovGminTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoritaSpreadStableSummandLieDecomposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem morita_spread_stable_summand_lie : ∀ {C : Type} [CommRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
  (m : ℕ) [NeZero m] (E : Fin m → Fin m → Module.End C H),
  (∀ i j k l, E i j * E k l = if j = k then E i l else 0) → ∑ i, E i i = 1 →
  ∀ {A : Type} [CommRing A] (σ : A →+* Module.End C H), (∀ i j c, E i j * σ c = σ c * E i j) →
  ∀ {O : Type} [Ring O] (ρ : O →+* Module.End C H),
  (∀ (c : O) i j (N : Submodule C H), (∀ c', ∀ x ∈ N, σ c' x ∈ N) → ∀ x ∈ N, E 0 0 x = x → E 0 i (ρ c (E j 0 x)) ∈ N) →
  ∀ (e : Module.End C H), e * e = e → (∀ i j, E i j * e = e * E i j) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ i j, ∀ x ∈ F, E i j x ∈ F) → (∀ x ∈ F, e x ∈ F) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (G₀ M₀ : Submodule C H), G₀ ⊓ M₀ = ⊥ → G₀ ⊔ M₀ = LinearMap.range (E 0 0 * e) →
    (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) → G₀ ⊔ I • LinearMap.range (E 0 0 * e) = F ⊓ LinearMap.range (E 0 0 * e) →
    (∀ d ∈ LinearMap.range (E 0 0 * e), ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀) →
  ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : O), ∀ x ∈ G, ρ c x ∈ G) ∧
    G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧
    ∀ d ∈ LinearMap.range e, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  intro C _ I H _ _ m _ E hE hsum A _ σ hσ O _ ρ hρ e he heE F hIF hFE hFe a χ G₀ M₀ hGM hGM' hσG hGF hLie
  have mul_ap : ∀ (f g : Module.End C H) x, (f * g) x = f (g x) := fun _ _ _ => rfl
  have app : ∀ i j k l x, E i j (E k l x) = if j = k then E i l x else 0 := by
    intro i j k l x
    rw [← mul_ap, hE]; split_ifs <;> simp
  have eapp : ∀ i j x, E i j (e x) = e (E i j x) := by
    intro i j x; rw [← mul_ap, heE, mul_ap]
  have sigcomm : ∀ i j c x, σ c (E i j x) = E i j (σ c x) := by
    intro i j c x; rw [← mul_ap, ← hσ, mul_ap]
  have ee : ∀ x, e (e x) = e x := fun x => by rw [← mul_ap, he]
  have memRe : ∀ x, x ∈ LinearMap.range e ↔ e x = x := by
    intro x; constructor
    · rintro ⟨y, rfl⟩; exact ee y
    · intro h; exact ⟨x, h⟩
  have memR00 : ∀ x, x ∈ LinearMap.range (E 0 0 * e) ↔ E 0 0 x = x ∧ e x = x := by
    intro x; constructor
    · rintro ⟨y, rfl⟩
      simp only [mul_ap]
      refine ⟨?_, ?_⟩
      · rw [app]; simp
      · rw [← eapp, ee]
    · rintro ⟨h1, h2⟩; exact ⟨x, by rw [mul_ap, h2, h1]⟩
  have decomp : ∀ x, ∑ i, E i 0 (E 0 i x) = x := by
    intro x
    calc ∑ i, E i 0 (E 0 i x) = ∑ i, E i i x := by simp [app]
      _ = (∑ i, E i i) x := (LinearMap.sum_apply _ _ _).symm
      _ = x := by rw [hsum]; rfl
  have E0i_mem : ∀ i x, e x = x → E 0 i x ∈ LinearMap.range (E 0 0 * e) := by
    intro i x hx; rw [memR00]
    exact ⟨by rw [app]; simp, by rw [← eapp, hx]⟩
  have hG0R : ∀ x ∈ G₀, E 0 0 x = x ∧ e x = x := fun x hx =>
    (memR00 x).1 (by rw [← hGM']; exact Submodule.mem_sup_left hx)
  have hM0R : ∀ x ∈ M₀, E 0 0 x = x ∧ e x = x := fun x hx =>
    (memR00 x).1 (by rw [← hGM']; exact Submodule.mem_sup_right hx)
  have hG₀F : ∀ g ∈ G₀, g ∈ F := fun g hg => by
    have h : g ∈ G₀ ⊔ I • LinearMap.range (E 0 0 * e) := Submodule.mem_sup_left hg
    rw [hGF] at h; exact h.1
  have spread_in : ∀ (N : Submodule C H) k, ∀ g ∈ N, E k 0 g ∈ ⨆ i, N.map (E i 0) :=
    fun N k g hg => Submodule.mem_iSup_of_mem k (Submodule.mem_map_of_mem hg)
  have spread_all : ∀ (N P : Submodule C H), (∀ k, ∀ g ∈ N, E k 0 g ∈ P) →
      (⨆ i, N.map (E i 0)) ≤ P :=
    fun N P h => iSup_le fun k => Submodule.map_le_iff_le_comap.2 fun g hg => h k g hg
  have spread_key : ∀ N : Submodule C H, (∀ x ∈ N, E 0 0 x = x) → ∀ j,
      ∀ x ∈ ⨆ i, N.map (E i 0), E 0 j x ∈ N := by
    intro N hN j x hx
    have : (⨆ i, N.map (E i 0)) ≤ N.comap (E 0 j) := by
      refine spread_all N _ fun k g hg => ?_
      simp only [Submodule.mem_comap]
      rw [app]
      split_ifs with h
      · subst h; rw [hN g hg]; exact hg
      · exact N.zero_mem
    exact this hx
  have spread_e : ∀ (N : Submodule C H), (∀ x ∈ N, e x = x) →
      (⨆ i, N.map (E i 0)) ≤ LinearMap.range e := fun N hN =>
    spread_all N _ fun k g hg => (memRe _).2 (by rw [← eapp, hN g hg])
  refine ⟨⨆ i, G₀.map (E i 0), ⨆ i, M₀.map (E i 0), ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxG, hxM⟩
    have h0 : ∀ i, E 0 i x = 0 := fun i => by
      have : E 0 i x ∈ G₀ ⊓ M₀ :=
        ⟨spread_key G₀ (fun y hy => (hG0R y hy).1) i x hxG,
         spread_key M₀ (fun y hy => (hM0R y hy).1) i x hxM⟩
      rw [hGM] at this; exact (Submodule.mem_bot C).1 this
    rw [Submodule.mem_bot, ← decomp x]; simp [h0]
  · refine le_antisymm (sup_le (spread_e G₀ fun y hy => (hG0R y hy).2)
      (spread_e M₀ fun y hy => (hM0R y hy).2)) ?_
    intro x hx
    rw [memRe] at hx
    rw [← decomp x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : E 0 i x ∈ G₀ ⊔ M₀ := by rw [hGM']; exact E0i_mem i x hx
    obtain ⟨g, hg, n, hn, hgn⟩ := Submodule.mem_sup.1 h1
    rw [← hgn, map_add (f := _)]
    exact Submodule.add_mem_sup (spread_in G₀ i g hg) (spread_in M₀ i n hn)
  · intro c x hx
    have key : ∀ j, E 0 j (ρ c x) ∈ G₀ := by
      intro j
      have : (⨆ i, G₀.map (E i 0)) ≤ G₀.comap (E 0 j * ρ c) :=
        spread_all G₀ _ fun k g hg => hρ c j k G₀ hσG g hg (hG0R g hg).1
      exact this hx
    rw [← decomp (ρ c x)]
    exact Submodule.sum_mem _ fun j _ => spread_in G₀ j _ (key j)
  · apply le_antisymm
    · refine sup_le ?_ (inf_le_inf_right _ hIF)
      refine spread_all G₀ _ fun k g hg => ⟨hFE k 0 g (hG₀F g hg), ?_⟩
      exact (memRe _).2 (by rw [← eapp, (hG0R g hg).2])
    · rintro x ⟨hxF, hxe⟩
      replace hxe := (memRe x).1 hxe
      rw [← decomp x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h1 : E 0 i x ∈ F ⊓ LinearMap.range (E 0 0 * e) := ⟨hFE 0 i x hxF, E0i_mem i x hxe⟩
      rw [← hGF] at h1
      obtain ⟨g, hg, t, ht, hgt⟩ := Submodule.mem_sup.1 h1
      rw [← hgt, map_add (f := _)]
      refine Submodule.add_mem_sup (spread_in G₀ i g hg) ?_
      have : I • LinearMap.range (E 0 0 * e) ≤ (I • ⊤ ⊓ LinearMap.range e).comap (E i 0) := by
        rw [Submodule.smul_le]
        intro r hr n hn
        rw [Submodule.mem_comap, map_smul]
        refine ⟨Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
        exact (memRe _).2 (by rw [map_smul, ← eapp, ((memR00 n).1 hn).2])
      exact this ht
  · intro d hd
    rw [memRe] at hd
    have hw : ∀ i, ∃ w : Fin a → H, (∀ j c, σ c (w j) - χ j c • w j ∈ G₀) ∧
        E 0 i d - ∑ j, w j ∈ G₀ := fun i => hLie _ (E0i_mem i d hd)
    choose w hw1 hw2 using hw
    refine ⟨fun j => ∑ i, E i 0 (w i j), ?_, ?_⟩
    · intro j c
      have : σ c (∑ i, E i 0 (w i j)) - χ j c • ∑ i, E i 0 (w i j) =
          ∑ i, E i 0 (σ c (w i j) - χ j c • w i j) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_sub, map_smul, Finset.smul_sum, Finset.sum_sub_distrib, sigcomm]
      rw [this]; exact Submodule.sum_mem _ fun i _ => spread_in G₀ i _ (hw1 i j c)
    · have : d - ∑ j, ∑ i, E i 0 (w i j) = ∑ i, E i 0 (E 0 i d - ∑ j, w i j) := by
        conv_lhs => rw [← decomp d]
        rw [Finset.sum_comm]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sub, map_sum, Finset.sum_sub_distrib]
      rw [this]; exact Submodule.sum_mem _ fun i _ => spread_in G₀ i _ (hw2 i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationLiftsSquareZeroSmoothLift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.MulLift

variable {S S' : Scheme.{0}}

theorem isPullback_tensor {A' B' : Over S'} {A B : Over S} {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsPullback f A'.hom A.hom b) (n : IsPullback g B'.hom B.hom b) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsPullback h (A' ⊗ B').hom (A ⊗ B).hom b := by
  have p : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  have p' : IsPullback (fst A' B').left (snd A' B').left A'.hom B'.hom := IsPullback.of_hasPullback _ _
  have q := p'.paste_horiz m
  rw [← h₁, ← n.w] at q
  have r := (IsPullback.of_right q h₂ p).paste_vert n
  rwa [Over.w, Over.w] at r

theorem smooth_tensor {X Y : Over S} (hX : Smooth X.hom) (hY : Smooth Y.hom) : Smooth (X ⊗ Y).hom := by
  haveI := hX
  haveI := hY
  rw [Over.tensorObj_hom, Limits.pullback.condition]
  infer_instance

theorem toUnit_left (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem lift_match {A : Over S'} {X : Over S} {i : A.left ⟶ X.left} {l : (A ⊗ A).left ⟶ (X ⊗ X).left}
    (hl₁ : l ≫ (fst X X).left = (fst A A).left ≫ i) (hl₂ : l ≫ (snd X X).left = (snd A A).left ≫ i)
    (u v : A ⟶ A) (U V : X ⟶ X) (hu : i ≫ U.left = u.left ≫ i) (hv : i ≫ V.left = v.left ≫ i) :
    i ≫ (lift U V).left = (lift u v).left ≫ l := by
  have p : IsPullback (fst X X).left (snd X X).left X.hom X.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [Category.assoc, ← Over.comp_left, lift_fst, hu, Category.assoc, hl₁, ← Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, hv, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left,
      lift_snd]

theorem one_match {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀} {A : Over (Sp R₀)} [GrpObj A]
    {X : Over (Sp R)} {i : A.left ⟶ X.left} (h : IsPullback i A.hom X.hom (spMap π)) {e : Sp R ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 _) (hie : (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A).left ≫ i = spMap π ≫ e) :
    i ≫ (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X)).left = (1 : A ⟶ A).left ≫ i := by
  have e₁ : (1 : 𝟙_ (Over (Sp R₀)) ⟶ A) = η[A] := by simp [Hom.one_def]
  change _ = (toUnit A ≫ η[A]).left ≫ i
  rw [Over.comp_left, Over.comp_left, toUnit_left, toUnit_left]
  change i ≫ X.hom ≫ e = (A.hom ≫ η[A].left) ≫ i
  rw [← Category.assoc i, h.w, Category.assoc, Category.assoc, ← e₁]
  exact congrArg (A.hom ≫ ·) hie.symm

end GlobalTheory.Obs.MulLift

namespace GlobalTheory.Obs


open MulLift in
theorem mul_lifts : FormSt → AxesVanishingExtendedDegOne → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left),
    IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom → ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left),
    l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∃ m : X ⊗ X ⟶ X, l ≫ m.left = (μ[A₀]).left ≫ i := by
  intro hF hAx R R₀ _ _ I hI π hπ hk A₀ _ g hab hg X i h hX e he hie l hl₁ hl₂
  have hl : IsPullback l (A₀ ⊗ A₀).hom (X ⊗ X).hom (spMap π) := isPullback_tensor h h hl₁ hl₂
  have hsm : Smooth (X ⊗ X).hom := smooth_tensor hX hX
  obtain ⟨S, ⟨P⟩⟩ := _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
  obtain ⟨S', ⟨P'⟩⟩ :=
    _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk (A₀ ⊗ A₀).left (A₀ ⊗ A₀).hom (X ⊗ X).left (X ⊗ X).hom l hl hsm
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := _root_.GlobalTheory.Obs.exists_aug R R₀ I hI π hπ hk
  have hh : (μ[A₀]).left ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀) := overW μ[A₀]
  have hlift : ∀ T : (Pair (μ[A₀]).left)ᵒᵖ,
      ∃ ρ : (ofSys S).B ((pairPull hh).G.obj T) →ₐ[R] (pairPre S' (μ[A₀]).left).B T,
        ∀ b, (pairPre S' (μ[A₀]).left).p T (ρ b) = (pairPull hh).α T ((ofSys S).p _ b) := fun T ↦ by
    haveI := (ofSys S).smooth ((pairPull hh).G.obj T)
    exact _root_.GlobalTheory.Obs.homLift R R₀ I hI π hπ hk _ _ ((ofSys S).p _) ((ofSys S).semi _) ((ofSys S).surj _)
      ((ofSys S).ker _) _ _ ((pairPre S' (μ[A₀]).left).p T) ((pairPre S' (μ[A₀]).left).semi T)
      ((pairPre S' (μ[A₀]).left).surj T) ((pairPre S' (μ[A₀]).left).ker T) (coefHom (pairPull hh) T)
  choose l₀ hl₀ using hlift
  have hL : (ofSys S).IsLift (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ := hl₀
  obtain ⟨Pp, Fa, -⟩ := hF R₀ A₀ g hab hg
  have hu : (lift (𝟙 A₀) 1).left ≫ (μ[A₀]).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one, Over.id_left]
  have hu' : (lift 1 (𝟙 A₀)).left ≫ (μ[A₀]).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.one_mul, Over.id_left]
  have hob : ∀ w, (ofSys S).IsOb1 (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ α w 0 := by
    intro w
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.Obs.exists_isOb1 R R₀ I hI π hπ hk R₁ α _ _ _ _ (ofSys S) (pairPre S' (μ[A₀]).left) (pairPull hh)
      l₀ (ofSys_isFun S) ((ofSys_isFun S').restrict _) hL w
    obtain ⟨⟨-, hsurj⟩, -⟩ := (_root_.GlobalTheory.Obs.PairExt.pairRes_ext_bijective R₀ R₁ _ _ (A₀ ⊗ A₀).hom (μ[A₀]).left).1
    obtain ⟨c', rfl⟩ := hsurj c
    have ax₁ : IsExtendedPullbackDegOne R₁ (overW (lift (𝟙 A₀) 1)) c' 0 :=
      _root_.GlobalTheory.Obs.retractionLiftObstruction_zero_of_liftedSection_alt R R₀ I hI π hπ hk R₁ α _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl S S' P P'
        (μ[A₀]).left hh (lift (𝟙 A₀) 1).left (overW _)
        (lift (𝟙 X) (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X))).left hu
        (Over.w _) (lift_match hl₁ hl₂ _ _ _ _ (by simp) (one_match h he hie)) l₀ hL w c' hc
    have ax₂ : IsExtendedPullbackDegOne R₁ (overW (lift 1 (𝟙 A₀))) c' 0 :=
      _root_.GlobalTheory.Obs.retractionLiftObstruction_zero_of_liftedSection_alt R R₀ I hI π hπ hk R₁ α _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl S S' P P'
        (μ[A₀]).left hh (lift 1 (𝟙 A₀)).left (overW _)
        (lift (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X)) (𝟙 X)).left hu'
        (Over.w _) (lift_match hl₁ hl₂ _ _ _ _ (one_match h he hie) (by simp)) l₀ hL w c' hc
    have h0 : c' = 0 := hAx R₀ R₁ α.q α.sq A₀ g hab hg c' ax₁ ax₂
    subst h0
    simpa using hc
  obtain ⟨l', hL', hN'⟩ := _root_.GlobalTheory.Obs.exists_natural_lift_of_ob1_eq_zero R R₀ I hI π hπ hk R₁ α A₀.left A₀.hom Pp Fa _ _ (ofSys S)
    (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ hL hob
  obtain ⟨f, hfs, hfk⟩ := _root_.GlobalTheory.Obs.pairs_glue R R₀ I hI π hπ hk _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl
    S S' P P' (μ[A₀]).left hh l' hL' hN'
  exact ⟨Over.homMk f hfs, hfk⟩

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqThetaConstantSpanningClassesLeExpStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_thetaConstant_spanning_classes_le_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ), GoodEmb c σ → IsUnf U → ∀ R : ℕ, Odd R → 1 < R → ∀ (xs : Fin (Dw.p + Dw.q) → GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : Rul Xo c), Submodule.span (𝓞 E) (Set.range xs) = ⊤ → GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f → ∀ (DF q m : ℕ) (R0 : ℝ), GlobalTheory.EtaAn.RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ z : Σ k, Frame (U.X k).Ψ r, z.2 ∈ (U.X z.1).dom → homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) z ≤ Real.exp ((GlobalTheory.EtaAn.p16 E r q m R 1 - ReciprocityTheory.ChartRestriction.G.I2.phiFD (U.X z.1) (ReciprocityTheory.ChartRestriction.G.I2.th (E := E) q R0) z.2) / (R : ℝ) ^ 4) := by
  first | exact @GlobalTheory.ThetaConst.normSq_thetaConst_le_exp | exact GlobalTheory.ThetaConst.normSq_thetaConst_le_exp | (intros; apply GlobalTheory.ThetaConst.normSq_thetaConst_le_exp <;> assumption)
end

