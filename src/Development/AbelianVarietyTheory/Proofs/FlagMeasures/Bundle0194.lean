module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBiorthogonalFrameOfSaturatedFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem exists_biorth {E : Type} [Field E] {n m : ℕ} {r : ℕ → ℕ}
    (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (hr : ∀ b, m ≤ b → r b = 0)
    (hn : n = ∑ b ∈ Finset.range m, r b)
    (hs : ∀ y : Fin n → E, ∃ u : ∀ b, Fin (r b) → E, y = ∑ b ∈ Finset.range m, T b *ᵥ u b) :
    ∃ T' : ∀ b, Matrix (Fin (r b)) (Fin n) E, Biorth r m T T' := by
  classical
  let Φ : ((b : Fin m) → Fin (r b) → E) →ₗ[E] (Fin n → E) :=
    ∑ b : Fin m, (T b).mulVecLin ∘ₗ LinearMap.proj b
  have hΦ : ∀ u : ∀ b, Fin (r b) → E, Φ (fun b => u b) = ∑ b ∈ Finset.range m, T b *ᵥ u b := by
    intro u
    rw [← Fin.sum_univ_eq_sum_range (fun b => T b *ᵥ u b)]
    simp [Φ]
  have hsurj : Function.Surjective Φ := fun y => by
    obtain ⟨u, hu⟩ := hs y
    exact ⟨_, (hΦ u).trans hu.symm⟩
  have hinj : Function.Injective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hn, Fin.sum_univ_eq_sum_range]
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let T' : ∀ b, Matrix (Fin (r b)) (Fin n) E := fun b =>
    if h : b < m then LinearMap.toMatrix'
      ((LinearMap.proj (⟨b, h⟩ : Fin m) : ((b : Fin m) → Fin (r b) → E) →ₗ[E] _) ∘ₗ e.symm.toLinearMap)
    else 0
  have hemp : ∀ b, ¬ b < m → IsEmpty (Fin (r b)) := fun b hb => by
    rw [hr b (by omega)]; infer_instance
  have hT' : ∀ (b : Fin m) y, T' b *ᵥ y = e.symm y b := fun b y => by
    simp only [T', dif_pos b.2]
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have H1 : ∀ (u : ∀ b, Fin (r b) → E) b, T' b *ᵥ (∑ c ∈ Finset.range m, T c *ᵥ u c) = u b := by
    intro u b
    by_cases hb : b < m
    · rw [hT' ⟨b, hb⟩, ← hΦ]
      exact congrFun (e.symm_apply_apply _) _
    · have := hemp b hb
      exact Subsingleton.elim _ _
  have H2 : ∀ b c v, T' b *ᵥ (T c *ᵥ v) = (Pi.single c v : ∀ b, Fin (r b) → E) b := by
    intro b c v
    rw [← H1 (Pi.single c v) b]
    congr 1
    by_cases hc : c < m
    · rw [Finset.sum_eq_single c (fun d _ hd => by simp [Pi.single_eq_of_ne hd])
        (fun h => absurd (Finset.mem_range.2 hc) h)]
      simp
    · have := hemp c hc
      obtain rfl : v = 0 := Subsingleton.elim _ _
      simp
  refine ⟨T', fun b => ?_, fun b c hbc => ?_, ?_⟩
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp [Pi.single_eq_of_ne hbc]
  · refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    obtain ⟨u, rfl⟩ := hs y
    simp only [Matrix.toLin'_apply]
    rw [Matrix.sum_mulVec, Matrix.one_mulVec]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Matrix.mulVec_mulVec, H1]

theorem exists_biorth_of_saturated_flag : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ), Monotone F → F 0 = ⊥ → (∀ b, m ≤ b → F b = F m) → Submodule.IsFullLattice E (F m) → (∀ b, ∀ y ∈ F m, y ∈ Submodule.span E (F b : Set (Fin n → E)) → y ∈ F b) → (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) → ∃ (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' ∧ (∀ b, Submodule.IsFullLattice E (Λ b)) ∧ ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0) := by
  intro E _ _ n m F r hmono h0 hm hL hsat hrk
  letI := hL
  have hle : ∀ b, F b ≤ F m := fun b => by
    rcases le_total b m with h | h
    · exact hmono h
    · exact (hm b h).le
  have key : ∀ b, ∃ A : Submodule (𝓞 E) (Fin n → E), A ⊓ F b = ⊥ ∧ A ⊔ F b = F (b + 1) := by
    intro b
    refine exists_compl_of_saturated _ _ (hmono b.le_succ) (Submodule.FG.of_le hL.fg (hle _)) ?_
    intro c y hc hy hcy
    apply hsat _ y (hle _ hy)
    have hc' : (c : E) ≠ 0 := by simpa using hc
    rw [← Submodule.smul_mem_iff _ hc']
    exact Submodule.subset_span hcy
  choose A hA1 hA2 using key
  have hAF : ∀ b, A b ≤ F (b + 1) := fun b => hA2 b ▸ le_sup_left
  have hAr : ∀ b, Formalism.HN.rkK (A b) = r b := fun b => by
    have := AdaptedExists.rkK_add (hA1 b)
    rw [hA2, hrk] at this
    omega
  choose Λ T hΛ hT using fun b => AdaptedExists.exists_model (A b)
    (Submodule.FG.of_le hL.fg ((hAF b).trans (hle _))) (hAr b)
  have hdec : ∀ k, ∀ y ∈ F k, ∃ u : ∀ b, Fin (r b) → E, (∀ b, u b ∈ Λ b) ∧
      y = ∑ b ∈ Finset.range k, T b *ᵥ u b := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [h0, Submodule.mem_bot] at hy
      exact ⟨0, fun b => zero_mem _, by simpa using hy⟩
    | succ k ih =>
      intro y hy
      rw [← hA2] at hy
      obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨v, hv, rfl⟩ := (hT k a).1 ha
      obtain ⟨u, hu, rfl⟩ := ih z hz
      refine ⟨Function.update u k v, fun b => ?_, ?_⟩
      · by_cases hb : b = k
        · subst hb; simpa using hv
        · rw [Function.update_of_ne hb]; exact hu b
      · rw [Finset.sum_range_succ, add_comm, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [Function.update_of_ne (Finset.mem_range.1 hc).ne]
  have hr0 : ∀ b, m ≤ b → r b = 0 := fun b hb => by
    have := hrk b
    rw [hm b hb, hm (b + 1) (by omega)] at this
    omega
  have hsum : ∀ k, Formalism.HN.rkK (F k) = ∑ b ∈ Finset.range k, r b := by
    intro k
    induction k with
    | zero => rw [h0]; simp [Formalism.HN.rkK]
    | succ k ih => rw [hrk, ih, Finset.sum_range_succ]
  have hn : n = ∑ b ∈ Finset.range m, r b := by
    rw [← hsum, Formalism.HN.rkK, Submodule.IsFullLattice.span_eq_top (A := E) (M := F m)]
    simp
  obtain ⟨T', hB⟩ := exists_biorth T hr0 hn (fun y => by
    obtain ⟨c, hc, hcy⟩ := AdaptedExists.exists_smul_mem (L := F m) (x := y)
      (by rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := F m)]; trivial)
    obtain ⟨u, -, hu⟩ := hdec m _ hcy
    have hc' : (c : E) ≠ 0 := by simpa using hc
    refine ⟨fun b => (c : E)⁻¹ • u b, ?_⟩
    simp only [Matrix.mulVec_smul]
    rw [← Finset.smul_sum, ← hu, eq_inv_smul_iff₀ hc']
    rfl)
  refine ⟨T, T', Λ, hB, hΛ, fun k y => ⟨fun hy b => ?_, fun hy => ?_⟩⟩
  · obtain ⟨u, hu, rfl⟩ := hdec k y hy
    have h1 : T' b *ᵥ (∑ c ∈ Finset.range k, T c *ᵥ u c) = if b < k then u b else 0 := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_mulVec]
      split_ifs with hb
      · rw [Finset.sum_eq_single b (fun c _ hc => by rw [hB.2.1 b c hc.symm, Matrix.zero_mulVec])
          (fun h => absurd (Finset.mem_range.2 hb) h), hB.1, Matrix.one_mulVec]
      · refine Finset.sum_eq_zero fun c hc => ?_
        rw [hB.2.1 b c (by have := Finset.mem_range.1 hc; omega), Matrix.zero_mulVec]
    rw [h1]
    refine ⟨?_, fun h => if_neg (by omega)⟩
    split_ifs
    · exact hu b
    · exact zero_mem _
  · have h1 : y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.sum_mulVec, hB.2.2, Matrix.one_mulVec]
    rw [h1]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · rw [(hy b).2 hb, Matrix.mulVec_zero]; exact zero_mem _
    · exact hmono (show b + 1 ≤ k by omega) (hAF b ((hT b _).2 ⟨_, (hy b).1, rfl⟩))

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundIpow
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.IdealFund

open GlobalTheory.HomCovolume

theorem exists_lat (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K) (ι : Type) [Fintype ι]
    (σ : ι → (K →+* ℂ)) (hσ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w)
    (a : FractionalIdeal (𝓞 K)⁰ K) (ha : a ≠ 0) :
    ∃ L : Submodule ℤ (ι → ℂ), (∀ z, z ∈ L ↔ ∃ y ∈ a, ∀ v, z v = σ v y) ∧
      HasCov volume L ((FractionalIdeal.absNorm a : ℝ) * Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) := by
  obtain ⟨L, hL, hcov⟩ := exists_idealLat K hK a ha
  let g : ι ≃ InfinitePlace K := Equiv.ofBijective (fun v => InfinitePlace.mk (σ v))
    ((Function.bijective_iff_existsUnique _).2 hσ)
  have hg : ∀ w, InfinitePlace.mk (σ (g.symm w)) = w := fun w => g.apply_symm_apply w
  have hκ : ∀ w : InfinitePlace K, ∃ κ : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ t, κ (σ (g.symm w) t) = w.embedding t := by
    intro w
    have h1 : InfinitePlace.mk (σ (g.symm w)) = InfinitePlace.mk w.embedding := by
      rw [hg, InfinitePlace.mk_embedding]
    rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
    · exact ⟨LinearIsometryEquiv.refl _ _, fun t => by rw [← h]; rfl⟩
    · exact ⟨Complex.conjLIE, fun t => by rw [← h]; rfl⟩
  choose κ hκ using hκ
  let e₀ : (ι → ℂ) ≃ₗ[ℝ] (InfinitePlace K → ℂ) :=
    { toFun := fun z w => κ w (z (g.symm w)), invFun := fun x v => (κ (g v)).symm (x (g v))
      map_add' := fun _ _ => funext fun w => by simp
      map_smul' := fun _ _ => funext fun w => by simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
      left_inv := fun _ => funext fun v => by simp
      right_inv := fun _ => funext fun w => by simp }
  have hcard : Fintype.card ι = Fintype.card (InfinitePlace K) := Fintype.card_congr g
  have hmp : MeasurePreserving e₀.toContinuousLinearEquiv volume volume := by
    refine measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · change ‖fun w => κ w (x (g.symm w))‖ ≤ 1 ↔ _
      simp only [pi_norm_le_iff_of_nonneg zero_le_one, LinearIsometryEquiv.norm_map]
      exact ⟨fun h v => by simpa using h (g v), fun h w => h _⟩
    · simp [volume_pi_closedBall _ zero_le_one, hcard]
  refine ⟨ZLattice.comap ℝ L e₀.toContinuousLinearEquiv.toLinearMap, fun z => ?_, ?_⟩
  · change e₀ z ∈ L ↔ _
    rw [hL]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h v => ?_, fun h w => ?_⟩
    · have h1 : κ (g v) (z (g.symm (g v))) = (g v).embedding y := h (g v)
      rw [← hκ] at h1
      simpa using h1
    · change κ w (z (g.symm w)) = _
      rw [h, hκ]
  · rw [hcard]
    exact HasCov.of_measurePreserving _ hmp (fun _ => Iff.rfl) hcov

theorem exists_fund_ipow : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)), IsPlaces σ → ∀ (𝔡 : Ideal (𝓞 K)) (n : ℤ) (c : ι → ℂ), 𝔡 ≠ ⊥ → (∀ v, c v ≠ 0) → ∃ F : Set (ι → ℂ), MeasurableSet F ∧ (∀ a : ι → ℂ, ∃! t : K, t ∈ ipow 𝔡 n ∧ ((fun v => c v * σ v t) + a) ∈ F) ∧ volume F = ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ∏ v, ‖c v‖ ^ 2) := by
  intro K _ _ _ hK ι _ σ hσ 𝔡 n c h𝔡 hc
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔡
  obtain ⟨L₀, hL₀, hcov⟩ := exists_lat K hK.1 ι σ hσ.2 _ (zpow_ne_zero n h0)
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
    LinearMap.pi fun v => (Algebra.lmul ℝ ℂ (c v)⁻¹).comp (LinearMap.proj v)
  have hf : ∀ z v, f z v = (c v)⁻¹ * z v := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ v, ‖c v‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
  have hpos : 0 < ∏ v, ‖c v‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hc v)) _
  let L : Submodule ℤ (ι → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ ∃ t ∈ ipow 𝔡 n, z = fun v => c v * σ v t := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => funext fun v => ?_, fun h v => ?_⟩
    · rw [← h, hf, mul_inv_cancel_left₀ (hc v)]
    · rw [hf, h, inv_mul_cancel_left₀ (hc v)]
  obtain ⟨v₀, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
  refine ⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := existsUnique_add_mem_latticeDomain L a
    obtain ⟨t, ht, hzt⟩ := (hL z).1 z.2
    refine ⟨t, ⟨ht, by rw [← hzt, add_comm]; exact hz⟩, ?_⟩
    rintro t' ⟨ht', h'⟩
    have h1 := hu ⟨_, (hL _).2 ⟨t', ht', rfl⟩⟩ (by rw [add_comm] at h'; exact h')
    have h2 := congrFun ((congrArg Subtype.val h1).trans hzt) v₀
    exact (σ v₀).injective (mul_left_cancel₀ (hc v₀) h2)
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos),
      div_inv_eq_mul, map_zpow₀, FractionalIdeal.coeIdeal_absNorm] at h
    have hfin : volume (latticeDomain L) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]
    congr 1
    push_cast
    ring

end GlobalTheory.IdealFund
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainEmbeddedRowsLattice
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.RowDomain

attribute [local instance] GlobalTheory.HomCovolume.haar_two GlobalTheory.HomCovolume.haar_three

noncomputable def rowLat (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) : Submodule ℤ (VecInf E k) :=
  AddSubgroup.toIntSubmodule
  { carrier := {z | ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ z = fun w b => w.embedding (τ b)}
    zero_mem' := ⟨0, fun y _ => by simp only [zero_dotProduct]; exact Λ₀.zero_mem, by funext w b; simp⟩
    add_mem' := by
      rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
      refine ⟨σ + τ, fun y hy => ?_, by funext w b; simp⟩
      have := Λ₀.add_mem (hσ y hy) (hτ y hy)
      convert this using 1
      funext _; simp
    neg_mem' := by
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨-τ, fun y hy => ?_, by funext w b; simp⟩
      have := Λ₀.neg_mem (hτ y hy)
      convert this using 1
      funext _; simp }

theorem mem_rowLat {E : Type} [Field E] [NumberField E] {k : ℕ} {Λ₀ : Submodule (𝓞 E) (Fin 1 → E)}
    {Λ' : Submodule (𝓞 E) (Fin k → E)} {z : VecInf E k} : z ∈ rowLat E k Λ₀ Λ' ↔
    ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ z = fun w b => w.embedding (τ b) := by
  rfl

theorem hasCov_rowLat (E : Type) [Field E] [NumberField E] (hE : IsTotallyComplex E) (k : ℕ)
    (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)) (h₀ : Submodule.IsFullLattice E Λ₀)
    (h' : Submodule.IsFullLattice E Λ') : GlobalTheory.HomCovolume.HasCov volume (rowLat E k Λ₀ Λ')
      (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k *
        (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) := by
  classical

  let e : VecInf E k ≃L[ℝ] (InfinitePlace E → Fin 1 → Fin k → ℂ) :=
    (LinearEquiv.piCongrRight fun _ : InfinitePlace E =>
      (LinearEquiv.funUnique (Fin 1) ℝ (Fin k → ℂ)).symm).toContinuousLinearEquiv
  have hes : ∀ x w b, e.symm x w b = x w 0 b := fun _ _ _ => rfl
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_pi fun _ : InfinitePlace E =>
      MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) (Fin k → ℂ))
  let L' : Submodule ℤ (InfinitePlace E → Fin 1 → Fin k → ℂ) :=
    (rowLat E k Λ₀ Λ').comap ((e.symm : _ →L[ℝ] VecInf E k).toLinearMap.restrictScalars ℤ)
  have hL' : ∀ z, z ∈ L' ↔ e.symm z ∈ rowLat E k Λ₀ Λ' := fun _ => Iff.rfl
  refine GlobalTheory.HomCovolume.HasCov.of_measurePreserving e hmp (L' := L')
    (fun x => by rw [hL', ContinuousLinearEquiv.symm_apply_apply]) ?_
  have hpos : ∀ j, 0 < detNorm E j (oneInf E j) := fun j => by rw [detNorm_oneInf]; exact one_pos
  obtain ⟨hd, hz, hc⟩ := GlobalTheory.HomCovolume.homCovolume E hE 1 k Λ₀ Λ' h₀ h' (oneInf E 1) (oneInf E k)
    (hpos 1) (hpos k) L' (by
      intro z
      rw [hL', mem_rowLat]
      simp only [of_oneInf, inv_one]
      constructor
      · rintro ⟨τ, hτ, hzτ⟩
        refine ⟨Matrix.of fun _ b => τ b, fun y hy => ?_, fun w => ?_⟩
        · exact hτ y hy
        · ext i b
          fin_cases i
          have := congrFun (congrFun hzτ w) b
          simpa [hes] using this
      · rintro ⟨T, hT, hTz⟩
        refine ⟨fun b => T 0 b, fun y hy => ?_, ?_⟩
        · convert hT y hy using 1
          funext i
          fin_cases i
          rfl
        · funext w b
          have := congrFun (congrFun (hTz w) 0) b
          simpa [hes] using this)
  exact ⟨hd, hz, by rw [hc, pow_one]⟩

theorem rowDomain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → ∃ P : Set (VecInf E k), MeasurableSet P ∧ volume P = ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) ∧ (∀ T : VecInf E k, ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ (fun w b => T w b + w.embedding (τ b)) ∈ P) ∧ ∀ (T : VecInf E k) (τ : Fin k → E), (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) → T ∈ P → (fun w b => T w b + w.embedding (τ b)) ∈ P → τ = 0 := by
  intro E _ _ hE k Λ₀ Λ' h₀ h'
  obtain ⟨hd, hz, hc⟩ := hasCov_rowLat E hE k Λ₀ Λ' h₀ h'

  let b := Module.Free.chooseBasis ℤ (rowLat E k Λ₀ Λ')
  have hspan := b.ofZLatticeBasis_span ℝ
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (VecInf E k))
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), ZSpan.fundamentalDomain_measurableSet _,
    ?_, fun T => ?_, fun T τ hτ hT hT' => ?_⟩
  · rw [← hc, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF]
    have hfin : (volume : Measure (VecInf E k)) (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top.ne
    exact (ofReal_measureReal hfin).symm
  · obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) T
    have hvL : (v : VecInf E k) ∈ rowLat E k Λ₀ Λ' := hspan.le v.2
    obtain ⟨τ, hτ, hvτ⟩ := mem_rowLat.1 hvL
    refine ⟨τ, hτ, ?_⟩
    convert hv using 1
    rw [Submodule.vadd_def, vadd_eq_add, hvτ]
    funext w b
    simp [add_comm]
  · have hzL : (fun (w : InfinitePlace E) (b : Fin k) => w.embedding (τ b)) ∈
        Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ)) :=
      hspan.ge (mem_rowLat.2 ⟨τ, hτ, rfl⟩)
    have hu := (ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) T).unique
      (y₁ := ⟨_, hzL⟩) (y₂ := 0) (by
        rw [Submodule.vadd_def, vadd_eq_add]
        convert hT' using 1
        funext w b
        simp [add_comm]) (by simpa using hT)
    have h0 : (fun (w : InfinitePlace E) (b : Fin k) => w.embedding (τ b)) = 0 :=
      congrArg Subtype.val hu
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    funext b
    have := congrFun (congrFun h0 w) b
    simpa using this

end GlobalTheory.RowDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermitianSqrtInSignedUnitaryGroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso


open scoped MatrixOrder ComplexOrder in
theorem exists_hermitian_sqrt_mul_mul_eq {n : ℕ} (J C : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J * J = 1) (hJh : Jᴴ = J) (hC : C.det ≠ 0)
    (h : (Cᴴ * C) * J * (Cᴴ * C) = J) :
    ∃ s : Matrix (Fin n) (Fin n) ℂ, IsUnit s.det ∧ sᴴ = s ∧ s * s = Cᴴ * C ∧ s * J * s = J :=
  by
  letI : PartialOrder ℂ := RCLike.toPartialOrder
  letI : PartialOrder (Matrix (Fin n) (Fin n) ℂ) := Matrix.instPartialOrder
  letI : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  letI : StarOrderedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instNonnegSpectrumClass
  set H := Cᴴ * C with hHdef
  have hH : 0 ≤ H := (Matrix.posSemidef_conjTranspose_mul_self C).nonneg
  set s := CFC.sqrt H with hsdef
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg H
  have hss : s * s = H := CFC.sqrt_mul_sqrt_self H hH
  have hsh : sᴴ = s := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (IsSelfAdjoint.of_nonneg hs0).star_eq
  have hdetH : H.det ≠ 0 := by
    rw [hHdef, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (star_ne_zero.mpr hC) hC
  have hdet : IsUnit s.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hdetH ?_
    rw [← hss, Matrix.det_mul, h0, zero_mul]
  refine ⟨s, hdet, hsh, hss, ?_⟩

  have hJHJ : H⁻¹ = J * H * J := by
    apply Matrix.inv_eq_right_inv
    calc H * (J * H * J) = H * J * H * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, hJ]

  have ht0 : 0 ≤ J * s * J := by
    have := star_left_conjugate_nonneg hs0 J
    rwa [Matrix.star_eq_conjTranspose, hJh] at this
  have hi0 : 0 ≤ s⁻¹ := hs0.posSemidef.inv.nonneg
  have htt : J * s * J * (J * s * J) = s⁻¹ * s⁻¹ := by
    rw [← Matrix.mul_inv_rev, hss, hJHJ, ← hss]
    calc J * s * J * (J * s * J) = J * s * (J * J) * s * J := by simp only [Matrix.mul_assoc]
      _ = J * (s * s) * J := by rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have heq : J * s * J = s⁻¹ := (CFC.mul_self_eq_mul_self_iff _ _ ht0 hi0).mp htt
  have h1 : s * (J * s * J) = 1 := by
    rw [heq]
    exact Matrix.mul_nonsing_inv s hdet
  calc s * J * s = s * (J * s * J) * J := by simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = J := by rw [h1, Matrix.one_mul]

theorem exists_hermitian_sqrt_mem_UJ (n : ℕ) (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : C.det ≠ 0) (h : (Cᴴ * C) * Formalism.REAL.Jm ε * (Cᴴ * C) = Formalism.REAL.Jm ε) :
    ∃ s : Formalism.REAL.UJ ε, (uMat s)ᴴ = uMat s ∧ uMat s * uMat s = Cᴴ * C := by
  obtain ⟨s, hdet, hsh, hss, hsJs⟩ := exists_hermitian_sqrt_mul_mul_eq (Formalism.REAL.Jm ε) C
    (Formalism.REAL.Jm_mul_self ε) (Formalism.REAL.Jm_conjTranspose ε) hC h
  have hu : IsUnit s := (Matrix.isUnit_iff_isUnit_det s).mpr hdet
  have hmem : hu.unit ∈ Formalism.REAL.UJ ε := by
    show (hu.unit : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * hu.unit = Formalism.REAL.Jm ε
    rw [IsUnit.unit_spec, hsh]
    exact hsJs
  refine ⟨⟨hu.unit, hmem⟩, ?_, ?_⟩
  · show (hu.unit : Matrix (Fin n) (Fin n) ℂ)ᴴ = hu.unit
    rw [IsUnit.unit_spec, hsh]
  · show (hu.unit : Matrix (Fin n) (Fin n) ℂ) * hu.unit = Cᴴ * C
    rw [IsUnit.unit_spec, hss]

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeft
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm

theorem map_haarGL_mul_left_eq : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (γ : MatInf E j), 0 < detNorm E j γ → (haarGL E j).map (fun g => γ * g) = haarGL E j :=
  fun E _ _ j γ h => (GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j γ h).2.map_eq

end GlobalTheory.OrbitTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLatticeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_infinitePlaceGaussian_lattice : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (L : Submodule ℤ (VecInf E j)) [DiscreteTopology L], IsZLattice ℝ L → Summable (fun x : L => gaussV E j x) ∧ Summable (fun y : dualAt E j L => gaussV E j y) ∧ ∑' x : L, gaussV E j x = (covAt E j L)⁻¹ * ∑' y : dualAt E j L, gaussV E j y ∧ ∫ x, gaussV E j x = 1 := by
  first | exact @GlobalTheory.FlagBase.poisson_gaussV | exact GlobalTheory.FlagBase.poisson_gaussV | (intros; apply GlobalTheory.FlagBase.poisson_gaussV <;> assumption)
end

