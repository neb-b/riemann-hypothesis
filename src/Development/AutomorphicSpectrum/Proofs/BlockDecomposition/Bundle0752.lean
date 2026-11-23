module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0575
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0750
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactClosureZpowersMap
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.TwSide

section Generic

variable {G : Type} [Group G]

end Generic

section Diag

variable {L : Type} [Field L]

theorem thetaGL_diagT (c : L →+* L) {n : ℕ} (u : Fin n → Lˣ) :
    thetaGL n c (GlobalTheory.SmGL.diagT L (Fin n) u) =
      GlobalTheory.SmGL.diagT L (Fin n) fun i => Units.map (c : L →* L) (u i.rev)⁻¹ := by
  apply Units.ext
  ext i j
  rw [GlobalTheory.ThetaPull.thetaGL_apply, ← map_inv, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), map_zero,
      mul_zero]

theorem exists_diagT {n : ℕ} (g : GL (Fin n) L) (h : ∀ i j : Fin n, i ≠ j → g.val i j = 0) :
    ∃ s : Fin n → Lˣ, g = GlobalTheory.SmGL.diagT L (Fin n) s := by
  have hne : ∀ i, g.val i i ≠ 0 := by
    intro i h0
    have h1 : (g.val * (g⁻¹).val) i i = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : i = k
      · subst hk
        rw [h0, zero_mul]
      · rw [h i k hk, zero_mul]
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij, h i j hij]

end Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_diagT_of_mem_TO {n : ℕ} {w : Pl E} {τ : GLw n w} (hτ : τ ∈ TO n w) :
    ∃ v : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (v i : w.adicCompletion E) = 1) ∧
      τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
  obtain ⟨v, hv⟩ := exists_diagT τ hτ.1
  refine ⟨v, fun i => ?_, hv⟩
  have h := hτ.2 i
  rw [hv, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq] at h
  exact h

theorem nrmL_diagT {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (u : Fin n → (w.adicCompletion E)ˣ) :
    nrmL n w (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u) =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n)
        fun i => u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ := by
  rw [nrmL, if_neg hw, thetaGL_diagT, ← map_mul]
  rfl

theorem ordL_norm_entry (hU : Unr E) {n : ℕ} {w : Pl E} (u : Fin n → (w.adicCompletion E)ˣ) (y : Fin n → ℤ)
    (hu : ∀ i, ordL (u i : w.adicCompletion E) = y i) (i : Fin n) :
    ordL ((u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = nv y i := by
  obtain ⟨-, -, hcv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hinv : ordL (((u i.rev)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    have h1 := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i.rev).ne_zero ((u i.rev)⁻¹).ne_zero
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one, hu] at h1
    omega
  have hmap : ordL ((Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    rw [← hinv]
    exact GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (hcv _)
  rw [Units.val_mul, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i).ne_zero (Units.ne_zero _), hu, hmap]
  simp only [nv]
  omega

end GlobalTheory.CompanionTheory.TwSide
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.CuspRep
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem v_thetaGL_apply (w : Pl E) (a : ℕ) (g : GLw a w) (i j : Fin a) :
    Valued.v ((thetaGL a (cj w) g).val i j) = Valued.v ((g⁻¹).val j.rev i.rev) := by
  rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, GlobalTheory.PrincCong.v_cj, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]

theorem thetaGL_mem_KGL (w : Pl E) (a : ℕ) {k : GLw a w} (hk : k ∈ GlobalTheory.LFun.KGL w (n := a)) :
    thetaGL a (cj w) k ∈ GlobalTheory.LFun.KGL w (n := a) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff w a k).1 hk
  refine (GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff w a _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [v_thetaGL_apply]
    exact h2 _ _
  · rw [← map_inv, v_thetaGL_apply, inv_inv]
    exact h1 _ _

theorem thetaGL_mem_iwGL (w : Pl E) (a : ℕ) {k : GLw a w} (hk : k ∈ iwGL a w) :
    thetaGL a (cj w) k ∈ iwGL a w := by
  obtain ⟨h1, h2, -⟩ := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a k).1).1 hk
  obtain ⟨-, -, h3⟩ := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a k⁻¹).1).1 (inv_mem hk)
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a _).1).2 ⟨fun i j => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [v_thetaGL_apply]
    exact h2 _ _
  · rw [← map_inv, v_thetaGL_apply, inv_inv]
    exact h1 _ _
  · rw [v_thetaGL_apply]
    exact h3 _ _ (Fin.rev_lt_rev.2 hij)

theorem isCompact_support_dcos (w : Pl E) (a : ℕ) (t : GLw a w) :
    IsCompact {g : GLw a w | dcos a w t g ≠ 0} := by
  have hI : IsCompact (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin a)
  have hS : IsCompact ((fun p : GLw a w × GLw a w => p.1 * t * p.2) ''
      ((iwGL a w : Set (GLw a w)) ×ˢ (iwGL a w : Set (GLw a w)))) :=
    (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  convert hS using 1
  ext g
  simp only [Set.mem_setOf_eq, dcos, Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists]
  constructor
  · intro h
    by_contra hn
    refine h (if_neg ?_)
    rintro ⟨x, hx, y, hy, rfl⟩
    exact hn ⟨x, y, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    rw [if_pos ⟨x, hx, y, hy, rfl⟩]
    exact one_ne_zero

end GlobalTheory.CompanionTheory.IwFacts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationQuotientSeparatedDvd
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SymmetricIndexRegularity

theorem orderEmb_rev {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S) (j : Fin m) :
    S.orderEmbOfFin h j.rev = (S.orderEmbOfFin h j).rev := by
  have key : (fun j : Fin m => (S.orderEmbOfFin h j.rev).rev) = S.orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique h
    · intro j
      exact hS _ (Finset.orderEmbOfFin_mem S h _)
    · intro i j hij
      exact Fin.rev_lt_rev.mpr ((S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hij))
  have := congrFun key j
  rw [← this, Fin.rev_rev]

theorem diff_injective {n : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) :
    Function.Injective fun i : Fin n => x i - x i.rev := by
  have : StrictAnti fun i : Fin n => x i - x i.rev := by
    intro i j hij
    have h1 := hx hij
    have h2 := hx (Fin.rev_lt_rev.mpr hij)
    show x j - x j.rev < x i - x i.rev
    omega
  exact this.injective

theorem nv_restr {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S)
    (j : Fin m) : nv (restr x S h) j = x (S.orderEmbOfFin h j) - x (S.orderEmbOfFin h j).rev := by
  simp only [nv, restr, orderEmb_rev S h hS]

theorem restr_strictAnti {n m : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) (S : Finset (Fin n)) (h : S.card = m) :
    StrictAnti (restr x S h) :=
  fun _ _ hij => hx ((S.orderEmbOfFin h).strictMono hij)

theorem mem_symIdx {n : ℕ} {mid : Prop} [Decidable mid] {s : Finset (Fin (n / 2))} {i : Fin n} :
    i ∈ symIdx n mid s ↔ (∃ h : i.val < n / 2, (⟨i.val, h⟩ : Fin (n / 2)) ∈ s) ∨
      (∃ h : n - 1 - i.val < n / 2, (⟨n - 1 - i.val, h⟩ : Fin (n / 2)) ∈ s) ∨ (mid ∧ n % 2 = 1 ∧ i.val = n / 2) := by
  simp [symIdx]

theorem symIdx_rev (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) :
    ∀ i ∈ symIdx n mid s, i.rev ∈ symIdx n mid s := by
  intro i hi
  have hv : i.rev.val = n - 1 - i.val := by
    have := i.isLt
    rw [Fin.val_rev]; omega
  have hv' : n - 1 - i.rev.val = i.val := by
    have := i.isLt
    omega
  rw [mem_symIdx] at hi ⊢
  rcases hi with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm, ho, he⟩
  · right; left
    refine ⟨by omega, ?_⟩
    simpa only [hv'] using hs
  · left
    refine ⟨by omega, ?_⟩
    simpa only [hv] using hs
  · right; right
    exact ⟨hm, ho, by omega⟩

theorem symIdx_disj (n : ℕ) (m₁ m₂ : Prop) [Decidable m₁] [Decidable m₂] (s : Finset (Fin (n / 2)))
    (hm : n % 2 = 1 → ¬ (m₁ ∧ m₂)) (i : Fin n) (h₁ : i ∈ symIdx n m₁ s) (h₂ : i ∈ symIdx n m₂ sᶜ) : False := by
  have hi := i.isLt
  rw [mem_symIdx] at h₁ h₂
  rcases h₁ with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm₁, ho, he⟩ <;> rcases h₂ with ⟨h', hs'⟩ | ⟨h', hs'⟩ | ⟨hm₂, ho', he'⟩
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact hm ho ⟨hm₁, hm₂⟩

theorem localization_quotient_separated_dvd {F : Type} [Field F] (ord : F → ℤ) {n a b : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x)
    (S₁ S₂ : Finset (Fin n)) (h₁ : S₁.card = a) (h₂ : S₂.card = b) (y₁ : ∀ i ∈ S₁, i.rev ∈ S₁)
    (y₂ : ∀ i ∈ S₂, i.rev ∈ S₂) (hd : ∀ i, i ∈ S₁ → i ∈ S₂ → False) (u₁ : Fin a → F) (u₂ : Fin b → F)
    (hu₁ : ∀ j, ord (u₁ j) = nv (restr x S₁ h₁) j) (hu₂ : ∀ j, ord (u₂ j) = nv (restr x S₂ h₂) j) :
    ((∏ i, (X - C (u₁ i))) * ∏ i, (X - C (u₂ i))).Separable := by
  have hprod : (∏ i, (X - C (u₁ i))) * (∏ i, (X - C (u₂ i))) = ∏ i, (X - C (Sum.elim u₁ u₂ i)) := by
    rw [Fintype.prod_sum_type]; simp
  rw [hprod, separable_prod_X_sub_C_iff]
  have hinj := diff_injective hx
  have e₁ : ∀ i j, u₁ i = u₁ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₁, nv_restr x S₁ h₁ y₁, nv_restr x S₁ h₁ y₁] at this
    exact (S₁.orderEmbOfFin h₁).injective (hinj this)
  have e₂ : ∀ i j, u₂ i = u₂ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₂, hu₂, nv_restr x S₂ h₂ y₂, nv_restr x S₂ h₂ y₂] at this
    exact (S₂.orderEmbOfFin h₂).injective (hinj this)
  have e₃ : ∀ i j, u₁ i = u₂ j → False := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₂, nv_restr x S₁ h₁ y₁, nv_restr x S₂ h₂ y₂] at this
    have h := hinj this
    refine hd _ (Finset.orderEmbOfFin_mem S₁ h₁ i) ?_
    rw [show S₁.orderEmbOfFin h₁ i = S₂.orderEmbOfFin h₂ j from h]
    exact Finset.orderEmbOfFin_mem S₂ h₂ j
  rintro (i | i) (j | j) hij
  · exact congrArg _ (e₁ _ _ hij)
  · exact (e₃ _ _ hij).elim
  · exact (e₃ _ _ hij.symm).elim
  · exact congrArg _ (e₂ _ _ hij)

end GlobalTheory.CompanionTheory.SymmetricIndexRegularity
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureZeroSetAvoidedByHolomorphicMap
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

section Abstract
open Set
open scoped ENNReal
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.FinChart

namespace GlobalTheory.CompanionTheory.ArchDom

theorem measurableSet_inter_preimage {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {f : α → β} {s : Set α}
    {t : Set β} (hf : ContinuousOn f s) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ f ⁻¹' t) := by
  have hm : Measurable (s.restrict f) := (continuousOn_iff_continuous_restrict.1 hf).measurable
  have := hs.subtype_image (hm ht)
  convert this using 1
  ext v
  exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩

theorem chartMeas_le_sum {D n : ℕ} {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (e : OpenPartialHomeomorph Y (V D)) (ρ : Y → ℝ≥0∞) {Z : Set Y}
    (hZ : MeasurableSet Z) (hnull : volume (e.target ∩ e.symm ⁻¹' Z) = 0)
    (P : Fin n → (Fin D → ℂ) → Y) (K : Fin n → Set (Fin D → ℂ)) (hK : ∀ j, MeasurableSet (K j))
    (hP : ∀ j, ContinuousOn (P j) (K j)) (w : Fin n → (Fin D → ℂ) → ℝ≥0∞)
    (hcov : ∀ y ∈ e.source, y ∉ Z → ∃ j, ∃ u ∈ K j, P j u = y)
    (hinj : ∀ j, ∀ u ∈ K j, ∀ u' ∈ K j, P j u ∉ Z → P j u = P j u' → u = u')
    (hdet : ∀ j, ∀ u ∈ K j, P j u ∈ e.source → P j u ∉ Z →
      DifferentiableAt ℝ ((toV D).symm ∘ e ∘ P j) u ∧
      ENNReal.ofReal |(fderiv ℝ ((toV D).symm ∘ e ∘ P j) u).det| * ρ (P j u) ≤ w j u) :
    GlobalTheory.ChartGlue.chartMeas e ρ ≤
      ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) := by
  refine Measure.le_iff.2 fun S hS => ?_
  have hsrc := e.open_source.measurableSet
  let T : Fin n → Set (Fin D → ℂ) := fun j => K j ∩ P j ⁻¹' ((e.source ∩ S) \ Z)
  let G : Fin n → (Fin D → ℂ) → (Fin D → ℂ) := fun j => (toV D).symm ∘ e ∘ P j
  have hT : ∀ j, MeasurableSet (T j) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) ((hsrc.inter hS).diff hZ)
  have hM : ∀ j, MeasurableSet (K j \ P j ⁻¹' Z) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) hZ.compl
  have hcover : e '' (e.source ∩ S) ⊆
      (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j) := by
    rintro _ ⟨y, ⟨hy, hyS⟩, rfl⟩
    by_cases hyZ : y ∈ Z
    · exact Or.inl (GlobalTheory.ChartGlue.mem_over e hy hyZ)
    · obtain ⟨j, u, hu, rfl⟩ := hcov y hy hyZ
      refine Or.inr (mem_iUnion.2 ⟨j, _, ⟨u, ⟨hu, ⟨⟨hy, hyS⟩, hyZ⟩⟩, rfl⟩, ?_⟩)
      simp [G]
  have hterm : ∀ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) ≤
      Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S := by
    intro j
    have hinjG : InjOn (G j) (T j) := by
      rintro u ⟨hu, hR⟩ u' ⟨hu', hR'⟩ h
      have h1 : e (P j u) = e (P j u') := (toV D).symm.injective h
      exact hinj j u hu u' hu' hR.2 (e.injOn hR.1.1 hR'.1.1 h1)
    have hder : ∀ u ∈ T j, HasFDerivWithinAt (G j) (fderiv ℝ (G j) u) (T j) u := fun u hu =>
      (hdet j u hu.1 hu.2.1.1 hu.2.2).1.hasFDerivAt.hasFDerivWithinAt
    have hae : AEMeasurable (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) :=
      (((hP j).mono diff_subset).aemeasurable (hM j)).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [← measurePreserving_toV.setLIntegral_comp_emb (toV D).toHomeomorph.measurableEmbedding,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hT j) hder hinjG,
      Measure.map_apply_of_aemeasurable hae hS, withDensity_apply',
      Measure.restrict_restrict' (hM j)]
    refine (setLIntegral_mono' (hT j) fun u hu => ?_).trans (lintegral_mono_set ?_)
    · have hv : toV D (G j u) = e (P j u) := (toV D).apply_symm_apply _
      have := (hdet j u hu.1 hu.2.1.1 hu.2.2).2
      rw [hv, e.left_inv hu.2.1.1]
      exact this
    · rintro u ⟨hu, hR⟩
      exact ⟨hR.1.2, hu, hR.2⟩
  calc GlobalTheory.ChartGlue.chartMeas e ρ S = ∫⁻ v in e '' (e.source ∩ S), ρ (e.symm v) :=
        GlobalTheory.ChartGlue.chartMeas_apply e ρ hS
    _ ≤ ∫⁻ v in (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ v in e.target ∩ e.symm ⁻¹' Z, ρ (e.symm v)) +
          ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := lintegral_union_le _ _ _
    _ = ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := by
        rw [setLIntegral_measure_zero _ _ hnull, zero_add]
    _ ≤ ∑' j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := lintegral_iUnion_le _ _
    _ = ∑ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := tsum_fintype _
    _ ≤ ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by rw [Measure.finsetSum_apply]

theorem ofReal_abs_norm_mul_le (d : ℂ) (x : ℝ) (ε : ℤˣ) :
    ENNReal.ofReal |Algebra.norm ℝ d| * ENNReal.ofReal ((ε : ℤ) * x) ≤
      ENNReal.ofReal |‖d‖ ^ 2 * x| := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity), abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖d‖ ^ 2)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using le_abs_self x
  · simpa using neg_le_abs x

end GlobalTheory.CompanionTheory.ArchDom
end Abstract


open GlobalTheory.FinChart in
theorem GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) →
    (∀ y, y ∉ Z → ∃ x, F x = y) → (∀ x x', F x ∉ Z → F x = F x' → x = x') →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (ε : ℤˣ) (K : Fin A.n → Set (Fin D → ℂ)),
    (∀ j, IsCompact (K j)) → (∀ j, K j ⊆ (A.chart j).target) →
    (∀ x, ∃ j, ∃ u ∈ K j, (A.chart j).symm u = x) →
    φ.chernPart D ε ≤ ∑ j, Measure.map (F ∘ (A.chart j).symm)
      ((volume.restrict (K j \ (F ∘ (A.chart j).symm) ⁻¹' Z)).withDensity fun u =>
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|) := by
  intro k _ X q σ D T _ A F hF hol Z hZ hnull hsurj hinj B φ hφ ε K hK hKt hKc
  refine iSup_le fun c => ?_
  refine GlobalTheory.CompanionTheory.ArchDom.chartMeas_le_sum c.e _ hZ (hnull c) (fun j => F ∘ (A.chart j).symm) K
    (fun j => (hK j).measurableSet)
    (fun j => hF.comp_continuousOn ((A.chart j).continuousOn_symm.mono (hKt j))) _ ?_ ?_ ?_
  · intro y _ hyZ
    obtain ⟨x, rfl⟩ := hsurj y hyZ
    obtain ⟨j, u, hu, rfl⟩ := hKc x
    exact ⟨j, u, hu, rfl⟩
  · intro j u hu u' hu' hZu h
    exact (A.chart j).symm.injOn (hKt j hu) (hKt j hu') (hinj _ _ hZu h)
  · intro j u hu hsrc _
    obtain ⟨han, hd⟩ := _root_.GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq A F hF hol φ hφ c j u (hKt j hu) hsrc
    have hG : (toV D).symm ∘ c.e ∘ (F ∘ (A.chart j).symm) =
        c.finChart ∘ F ∘ (A.chart j).symm := rfl
    rw [hG]
    have hdiff := han.differentiableAt
    refine ⟨hdiff.restrictScalars ℝ, ?_⟩
    have hdet : (fderiv ℝ (c.finChart ∘ F ∘ (A.chart j).symm) u).det = Algebra.norm ℝ
        (LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) := by
      rw [hdiff.fderiv_restrictScalars ℝ]
      exact LinearMap.det_restrictScalars
        (f := (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, hd]
    exact GlobalTheory.CompanionTheory.ArchDom.ofReal_abs_norm_mul_le _ _ ε
end

