module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0054
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CardKPNeZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug.TwistLevels

open Formalism.L2.Host

theorem not_unrAt_mul {L : Type} [Field L] [NumberField L] {d ψ : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (hd : d.UnrAt v) (hψ : ¬ ψ.UnrAt v) : ¬ (d * ψ).UnrAt v := by
  intro h
  apply hψ
  intro x hx
  have := h x hx
  change d.loc v x * ψ.loc v x = 1 at this
  rw [hd x hx, one_mul] at this
  exact this

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {d ψ : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (hd : d.UnrAt v) (hψ : ψ.UnrAt v) : (d * ψ).UnrAt v := by
  intro x hx
  change d.loc v x * ψ.loc v x = 1
  rw [hd x hx, hψ x hx, one_mul]

theorem card_residueField_ne_zero {L : Type} [Field L] [NumberField L] (Q : HeightOneSpectrum (𝓞 L)) : Nat.card (kP Q) ≠ 0 := by
  have h : Nat.card (kP Q) = Ideal.absNorm Q.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h, Ne, Ideal.absNorm_eq_zero_iff]
  exact Q.ne_bot

def ramSet (P : Pre) (Ξ : Set (HChar P.host.E)) : Set (HeightOneSpectrum (𝓞 P.host.E)) :=
  {Q | ((P.host.pde * P.host.pde' : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal ∨ ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}

theorem not_unrAt_xiTw (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E))
    (hQ : Q ∈ T.Q w) (hn : ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) : ¬ (T.xiTw f w).UnrAt Q := by
  have h1 : ((B.host.pde : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_right _ h)
  have h2 : ((B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_left _ h)
  have hψ : ¬ (T.psi w).UnrAt Q := fun h => ((T.psi_is w).ram Q).1 h hQ
  unfold TwDat.xiTw
  split_ifs
  · exact not_unrAt_mul (f.isDel'.unr Q h2) hψ
  · exact not_unrAt_mul (f.isDel.unr Q h1) hψ

theorem ram_finite (B : Base) (f : Fr B.toPre) (T : TwDat B) (χ : HChar B.host.E) (hχ : χ ∈ T.set f) :
    {Q : HeightOneSpectrum (𝓞 B.host.E) | ¬ χ.UnrAt Q}.Finite := by
  have hpde : B.host.pde * B.host.pde' ≠ 0 :=
    mul_ne_zero (B.toPre.level_prime _ B.host.pde_level.1).ne_zero (B.toPre.level_prime _ B.host.pde_level.2).ne_zero
  have hZ := GlobalTheory.Mem.Top.TwFin.finite_mem (K := B.host.E) hpde
  have h1 : ∀ Q : HeightOneSpectrum (𝓞 B.host.E), ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal →
      ((B.host.pde : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun Q hn h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_right _ h)
  have h2 : ∀ Q : HeightOneSpectrum (𝓞 B.host.E), ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal →
      ((B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun Q hn h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_left _ h)
  rcases hχ with hχ | ⟨w, rfl⟩
  · rcases hχ with rfl | rfl | rfl
    · exact Set.finite_empty.subset fun Q hQ => hQ fun _ _ => rfl
    · refine hZ.subset fun Q hQ => ?_
      by_contra hn
      exact hQ (f.isDel.unr Q (h1 Q hn))
    · refine hZ.subset fun Q hQ => ?_
      by_contra hn
      exact hQ (f.isDel'.unr Q (h2 Q hn))
  · refine (hZ.union (T.Q w).finite_toSet).subset fun Q hQ => ?_
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hc
    have hψ : (T.psi w).UnrAt Q := ((T.psi_is w).ram Q).2 hc.2
    apply hQ
    unfold TwDat.xiTw
    split_ifs
    · exact unrAt_mul (f.isDel'.unr Q (h2 Q hc.1)) hψ
    · exact unrAt_mul (f.isDel.unr Q (h1 Q hc.1)) hψ


open Classical in
theorem levels_bounded : ∀ (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)), ∃ Ms : Finset ℕ, (∀ M ∈ Ms, M ≠ 0) ∧
    ∀ (B : Base) (hB : B.toPre = P) (T : TwDat B), HEq (T.set (hB ▸ f)) Ξ → ∀ (w : B.places.Pl)
      (S : Finset (HeightOneSpectrum (𝓞 B.host.E))),
      (∀ Q ∈ S, ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal ∨ Q ∈ T.Q w) →
      B.host.g 0 * B.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q ∈ Ms := by
  intro P f Ξ
  by_cases hA : (ramSet P Ξ).Finite
  · refine ⟨hA.toFinset.powerset.image
      (fun S => P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q), ?_, ?_⟩
    · intro M hM
      obtain ⟨S, -, rfl⟩ := Finset.mem_image.1 hM
      refine mul_ne_zero (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero) ?_
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hq
      exact card_residueField_ne_zero Q
    · intro B hB T hT w S hS
      subst hB
      have hT' : T.set f = Ξ := eq_of_heq hT
      refine Finset.mem_image.2 ⟨S, Finset.mem_powerset.2 fun Q hQ => hA.mem_toFinset.2 ?_, rfl⟩
      rcases hS Q hQ with h | h
      · exact Or.inl h
      · by_cases hn : ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal
        · exact Or.inl hn
        · refine Or.inr ⟨T.xiTw f w, ?_, not_unrAt_xiTw B f T w Q h hn⟩
          rw [← hT']
          exact Set.mem_union_right _ ⟨w, rfl⟩
  · refine ⟨∅, by simp, ?_⟩
    intro B hB T hT w S hS
    subst hB
    exfalso
    apply hA
    have hT' : T.set f = Ξ := eq_of_heq hT
    have hpde : B.host.pde * B.host.pde' ≠ 0 :=
      mul_ne_zero (B.toPre.level_prime _ B.host.pde_level.1).ne_zero (B.toPre.level_prime _ B.host.pde_level.2).ne_zero
    have hfin := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
    refine ((GlobalTheory.Mem.Top.TwFin.finite_mem (K := B.host.E) hpde).union
      (hfin.biUnion fun χ hχ => ram_finite B f T χ hχ)).subset ?_
    rintro Q (h | ⟨χ, hχ, hr⟩)
    · exact Or.inl h
    · refine Or.inr (Set.mem_biUnion (x := χ) ?_ hr)
      rw [hT']
      exact hχ

end GlobalTheory.Plug.TwistLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoeffSeriesOfKTypeProjections
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeSum.KSeries

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem coef_eq_fam (h : Std ε σ) {p : ℕ} {ℓ : Fin p → (H →ₗ[ℂ] ℂ)} {x : Fin p → H}
    (hℓ : ∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) (hx : ∀ j, Sm ε σ (x j)) {Φ : List (Mx n) → Mx n → ℂ}
    (h0 : ∀ y ∈ UJset ε, Φ [] y = ∑ j, ℓ j (σ y (x j)))
    (hd : ∀ (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
      ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ l (y * NormedSpace.exp (t • X))) (Φ (X :: l) y) 0) :
    ∀ w : List (Mx n), (∀ Y ∈ w, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ y ∈ UJset ε,
      Φ w y = ∑ j, ℓ j (σ y (Dw σ w (x j))) := by
  intro w
  induction w with
  | nil => intro _ y hy; simpa [Dw] using h0 y hy
  | cons X l ih =>
    intro hw y hy
    have hX := hw X List.mem_cons_self
    have hl : ∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hlL : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => (hl Y hY).1
    have d1 := hd l hl X hX.1 hX.2 y hy
    have d2 : HasDerivAt (fun t : ℝ => ∑ j, ℓ j (σ (y * NormedSpace.exp (t • X)) (Dw σ l (x j))))
        (∑ j, ℓ j (σ (y * NormedSpace.exp ((0 : ℝ) • X)) (dRep σ X (Dw σ l (x j))))) 0 :=
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ => GlobalTheory.TypeSum.CoefLow.hasDerivAt_coef h (hℓ j) ((hx j).word h.1 hlL) hX.1 hy 0
    have e : (fun t : ℝ => Φ l (y * NormedSpace.exp (t • X))) =
        fun t => ∑ j, ℓ j (σ (y * NormedSpace.exp (t • X)) (Dw σ l (x j))) := by
      funext t; exact ih hl _ (mul_mem_UJ hy (exp_mem_UJ hX.1 t))
    rw [e] at d1
    rw [d1.unique d2]
    simp [Dw]

end GlobalTheory.TypeSum.KSeries

namespace GlobalTheory.TypeSum.KSeries

def pad {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) : ℕ × ℕ → α :=
  fun p => if h : p.2 < q p.1 then a p.1 ⟨p.2, h⟩ else 0

theorem pad_of_lt {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) {i r : ℕ} (h : r < q i) :
    pad q a (i, r) = a i ⟨r, h⟩ := dif_pos h

theorem pad_of_ge {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) {i r : ℕ} (h : ¬ r < q i) :
    pad q a (i, r) = 0 := dif_neg h

theorem pad_hasSum_fiber {α : Type} [AddCommMonoid α] [TopologicalSpace α] (q : ℕ → ℕ)
    (a : (i : ℕ) → Fin (q i) → α) (i : ℕ) : HasSum (fun r => pad q a (i, r)) (∑ r, a i r) := by
  have h1 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := Finset.range (q i))
    (f := fun r => pad q a (i, r)) (fun r hr => pad_of_ge q a fun h => hr (Finset.mem_range.2 h))
  convert h1 using 1
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun r _ => (pad_of_lt q a r.isLt).symm

theorem pad_summable (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → ℝ) (ha : ∀ i r, 0 ≤ a i r) (b : ℕ → ℝ)
    (hb : Summable b) (hle : ∀ i, ∑ r, a i r ≤ b i) : Summable (pad q a) := by
  have nn : 0 ≤ pad q a := fun p => by
    simp only [pad, Pi.zero_apply]; split_ifs
    · exact ha _ _
    · exact le_rfl
  rw [summable_prod_of_nonneg nn]
  refine ⟨fun i => (pad_hasSum_fiber q a i).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun i => tsum_nonneg fun r => nn _) (fun i => ?_) hb
  rw [(pad_hasSum_fiber q a i).tsum_eq]
  exact hle i

theorem pad_hasSum (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → ℂ) (hs : Summable fun p => ‖pad q a p‖) {F : ℂ}
    (hF : HasSum (fun i => ∑ r, a i r) F) : HasSum (pad q a) F := by
  have hs' : Summable (pad q a) := hs.of_norm
  have h3 : ∑' p, pad q a p = F := (hs'.hasSum.prod_fiberwise (pad_hasSum_fiber q a)).unique hF
  rw [← h3]
  exact hs'.hasSum

end GlobalTheory.TypeSum.KSeries

namespace GlobalTheory.TypeSum.KSeries

set_option maxHeartbeats 1000000 in
theorem hasTypeAll_of_kTypes : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (x : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, IsKFin ε σ (x j)) ∧
        ∀ y ∈ UJset ε, (∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) = ∑ j, ℓ j (σ y (x j))) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.SmoothGlob.lieSet ε) (UJset ε) σ f := by
  intro hHC hCW n ε H _ _ _ σ hσ f hf hU hyp
  obtain ⟨e, he1, he2, hP⟩ := _root_.GlobalTheory.KFourier.exists_rightKFourier n ε
  obtain ⟨N, Φ, B, hΦ0, hΦd, hΦb, hBs, hsum⟩ := hP f hf hU
  obtain ⟨S, hS, m, A, hQ⟩ := _root_.GlobalTheory.TypeSum.CoefRep.exists_rewrite hHC hCW n ε H σ hσ N
  choose p ℓ x hℓ hx heq using fun i => hyp (e i) (he1 i) (he2 i)
  have hbound : ∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ i j (σ y (Dw σ w (x i j)))‖ ≤ B i k * (1 + hs y) ^ N := by
    intro i k w hk hw y hy
    rw [← coef_eq_fam hσ (hℓ i) (fun j => hσ.2.2.1 _ (hx i j)) (fun y hy => (hΦ0 i y hy).trans (heq i y hy))
      (hΦd i) w (fun Y hY => ⟨(hw Y hY).1, (hw Y hY).2.1⟩) y hy]
    exact hΦb i k w hk hw y hy
  choose q ℓ' x' c hx' hc hℓ' hsumS heq' using fun i => hQ (p i) (ℓ i) (x i) (hℓ i) (hx i) (B i) (hbound i)
  obtain ⟨S₁, hS₁, -, ⟨Bc, hBc, hctrl⟩, A₀, hA₀, hdom⟩ := GlobalTheory.TypeSumCtrl.exists_ctrl n ε H σ hσ S hS
  have hV : ∀ a, Sm ε σ (pad q x' a) := fun a => by
    simp only [pad]; split_ifs
    · exact hx' _ _
    · exact sm_iff.2 (Submodule.zero_mem _)
  have key : ∀ S', Words (lieSet ε) S' →
      Summable (fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a)) := by
    intro S' hS'
    have e1 : (fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a)) =
        pad q (fun i r => A₀ * c i r * sobNorm σ S' (x' i r)) := by
      funext a; simp only [pad]; split_ifs <;> simp
    rw [e1]
    refine pad_summable q _ (fun i r => mul_nonneg (mul_nonneg hA₀ (hc i r)) (sobNorm_nonneg _ _ _))
      (fun i => A₀ * A S' * B i (m S')) ((hBs (m S')).mul_left (A₀ * A S')) fun i => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hsumS i S' hS') hA₀
  have hnorm : ∀ g ∈ UJset ε, ∀ a, ‖pad q (fun i r => ℓ' i r (σ g (x' i r))) a‖ ≤
      Bc g * (pad q (fun i r => A₀ * c i r) a * sobNorm σ S₁ (pad q x' a)) := by
    intro g hg a
    simp only [pad]
    split_ifs with h
    · have hs1 := (hx' a.1 ⟨a.2, h⟩).translate hσ.1 hg
      calc ‖ℓ' a.1 ⟨a.2, h⟩ (σ g (x' a.1 ⟨a.2, h⟩))‖
          ≤ c a.1 ⟨a.2, h⟩ * sobNorm σ S (σ g (x' a.1 ⟨a.2, h⟩)) := hℓ' _ _ _ hs1
        _ ≤ c a.1 ⟨a.2, h⟩ * (A₀ * sobNorm σ S₁ (σ g (x' a.1 ⟨a.2, h⟩))) :=
          mul_le_mul_of_nonneg_left (hdom _ hs1) (hc _ _)
        _ ≤ c a.1 ⟨a.2, h⟩ * (A₀ * (Bc g * sobNorm σ S₁ (x' a.1 ⟨a.2, h⟩))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hctrl g hg _ (hx' _ _)) hA₀) (hc _ _)
        _ = Bc g * (A₀ * c a.1 ⟨a.2, h⟩ * sobNorm σ S₁ (x' a.1 ⟨a.2, h⟩)) := by ring
    · simp
  have hterm : ∀ g a, pad q ℓ' a (σ g (pad q x' a)) = pad q (fun i r => ℓ' i r (σ g (x' i r))) a := by
    intro g a; simp only [pad]; split_ifs <;> simp
  have hsum2 : ∀ g ∈ UJset ε, HasSum (fun a : ℕ × ℕ => pad q ℓ' a (σ g (pad q x' a))) (f g) := by
    intro g hg
    simp only [hterm]
    refine pad_hasSum q _ (Summable.of_nonneg_of_le (fun a => norm_nonneg _) (hnorm g hg)
      ((key S₁ hS₁).mul_left (Bc g))) ?_
    refine (hsum g hg).congr_fun fun i => ?_
    rw [heq i g hg, heq' i g hg]
  refine ⟨S₁, hS₁, ⟨Bc, hBc, hctrl⟩, pad q x' ∘ Nat.pairEquiv.symm, pad q ℓ' ∘ Nat.pairEquiv.symm,
    pad q (fun i r => A₀ * c i r) ∘ Nat.pairEquiv.symm, ⟨⟨fun k => hV _, fun k => ?_, fun k w hw => ?_, ?_, fun g hg => ?_⟩, fun S' hS' => ?_⟩⟩
  · show 0 ≤ pad q (fun i r => A₀ * c i r) (Nat.pairEquiv.symm k)
    simp only [pad]; split_ifs
    · exact mul_nonneg hA₀ (hc _ _)
    · exact le_rfl
  · show ‖pad q ℓ' (Nat.pairEquiv.symm k) w‖ ≤ pad q (fun i r => A₀ * c i r) (Nat.pairEquiv.symm k) * sobNorm σ S₁ w
    simp only [pad]; split_ifs with h
    · calc ‖ℓ' _ _ w‖ ≤ c _ ⟨_, h⟩ * sobNorm σ S w := hℓ' _ _ _ hw
        _ ≤ c _ ⟨_, h⟩ * (A₀ * sobNorm σ S₁ w) := mul_le_mul_of_nonneg_left (hdom _ hw) (hc _ _)
        _ = A₀ * c _ ⟨_, h⟩ * sobNorm σ S₁ w := by ring
    · simp
  · exact (Nat.pairEquiv.symm.summable_iff (f := fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S₁ (pad q x' a))).2 (key S₁ hS₁)
  · exact (Nat.pairEquiv.symm.hasSum_iff (f := fun a : ℕ × ℕ => pad q ℓ' a (σ g (pad q x' a)))).2 (hsum2 g hg)
  · exact (Nat.pairEquiv.symm.summable_iff (f := fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a))).2 (key S' hS')

end GlobalTheory.TypeSum.KSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField
section
noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open scoped IntermediateField

theorem curveOver_of_weberSet (D : D7) (F : IntermediateField ℚ ℂ) {n : ℕ} (hn : 0 < n)
    (h0 : D.host.φ₀ D.host.sqrtMinusD ∈ F)
    (h : ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔
      ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + D.host.φ₀ D.host.sqrtMinusD) / 2)) → weberSet L n ⊆ F) :
    GlobalTheory.CompRat.CurveOver (hostOfRecord D) F n :=
  (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ (hostOfRecord D) F n hn).1 h0 fun L hL =>
    ⟨h L hL (Set.mem_insert _ _), fun s hs =>
      h L hL (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩


end GlobalTheory.FieldSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem weberSet_finite (L : PeriodPair) {n : ℕ} (hn : 0 < n) : (weberSet L n).Finite := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  let f : ℤ × ℤ → ℂ := fun s => L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) *
    L.weierstrassP ((s.1 * L.ω₁ + s.2 * L.ω₂) / n)
  refine Set.Finite.insert _
    ((((Set.finite_Ico (0 : ℤ) n).prod (Set.finite_Ico (0 : ℤ) n)).image f).subset ?_)
  rintro _ ⟨z, hz, -, rfl⟩
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
  refine ⟨(a % n, b % n), ⟨⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩,
    ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩⟩, ?_⟩
  have e : (a * L.ω₁ + b * L.ω₂) / n = (((a % n : ℤ) : ℂ) * L.ω₁ + ((b % n : ℤ) : ℂ) * L.ω₂) / n +
      (((a / n : ℤ) : ℂ) * L.ω₁ + ((b / n : ℤ) : ℂ) * L.ω₂) := by
    have a1 : ((a % n : ℤ) : ℂ) + n * ((a / n : ℤ) : ℂ) = a := by
      exact_mod_cast Int.emod_add_mul_ediv a n
    have a2 : ((b % n : ℤ) : ℂ) + n * ((b / n : ℤ) : ℂ) = b := by
      exact_mod_cast Int.emod_add_mul_ediv b n
    rw [← a1, ← a2]
    field_simp
    ring
  simp only [f]
  rw [e, L.weierstrassP_add_coe _ ⟨_, PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩⟩]

theorem exists_map_weber_eq (L : PeriodPair) (n : ℕ) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) (τ : ℂ ≃+* ℂ)
    (hτ : τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2))
    (t : ℂ) (hnt : (n : ℂ) * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧
      τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) =
        L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t' := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  set J := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hJ
  set u := L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hu
  have hu0 : u ≠ 0 := div_ne_zero (mul_ne_zero h2 h3) hD
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hu0 (by simpa using hm.symm)
  have hmu : (m ^ 2)⁻¹ = u := by rw [hm, inv_inv]
  have H := isHomothetic_scalePeriods L m hm0
  set L' := scalePeriods L m hm0
  have hJ1 : J - 1 = 27 * L.g₃ ^ 2 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [hJ, div_sub_one hD, sub_sub_cancel]
  have e2 : L'.g₂ = J * (J - 1) / 27 := by
    rw [H.g₂_eq, show (m ^ 4)⁻¹ = ((m ^ 2)⁻¹) ^ 2 by ring, hmu, hJ1, hu, hJ]
    generalize L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = D
    ring
  have e3 : L'.g₃ = J * (J - 1) ^ 2 / 729 := by
    rw [H.g₃_eq, show (m ^ 6)⁻¹ = ((m ^ 2)⁻¹) ^ 3 by ring, hmu, hJ1, hu, hJ]
    generalize L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = D
    ring
  have f2 : L'.g₂ = τ L'.g₂ := by
    rw [e2]; simp [hτ, map_ofNat]
  have f3 : L'.g₃ = τ L'.g₃ := by
    rw [e3]; simp [hτ, map_ofNat]
  obtain ⟨s, -, hc⟩ := GlobalTheory.ConjPoint.exists_conjEquiv f2 f3
  obtain ⟨w, hw⟩ := latticePoint_surjective L' (s (latticePoint L' (m * t)))
  obtain ⟨t', rfl⟩ : ∃ t', w = m * t' := ⟨m⁻¹ * w, by field_simp⟩
  have hconj := (hc _ _).2 hw.symm
  have h1 := (hconj.nsmul_mem_iff f2 f3 n).1 (by rw [mul_left_comm]; exact (H _).2 hnt)
  rw [mul_left_comm] at h1
  obtain ⟨-, h4, h5, -⟩ := hconj.resolve_left fun h => ht ((H t).1 h.1)
  refine ⟨t', (H _).1 h1, fun h => h4 ((H _).2 h), ?_⟩
  rw [H.weierstrassP_mul, H.weierstrassP_mul, hmu] at h5
  exact h5.symm

theorem weberSet_finite_algebraic_permuted : ∀ (L : PeriodPair) (n : ℕ), 0 < n → L.g₂ ≠ 0 → L.g₃ ≠ 0 → (weberSet L n).Finite ∧ (IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ w ∈ weberSet L n, IsAlgebraic ℚ w) ∧ ∀ τ : ℂ ≃+* ℂ, τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ t, (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice → ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧ τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) = (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') := by
  intro L n hn h2 h3
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  refine ⟨weberSet_finite L hn, fun hj => ?_, exists_map_weber_eq L n h2 h3⟩
  rintro _ (rfl | ⟨z, hz, hz', rfl⟩)
  · exact hj
  · exact GlobalTheory.WeberField.weber_isAlgebraic L hj hn hz' (by rwa [mul_div_cancel₀ _ hn0])

end GlobalTheory.FieldSize
end

