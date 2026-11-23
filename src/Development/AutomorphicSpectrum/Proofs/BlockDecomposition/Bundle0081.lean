module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0064
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDualFamilyHolds
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionSquareIdentity
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

open Polynomial

variable {m : ℕ}

noncomputable def pfPoly (x : ℝ) (r d' : Fin m → ℝ) : ℝ[X] :=
  (X - C x) * ∏ j, (X - C (d' j)) + ∑ j, C (r j) * ∏ k ∈ univ.erase j, (X - C (d' k))

lemma eval_pfPoly (x : ℝ) (r d' : Fin m → ℝ) (s : ℝ) (hs : ∀ j, s - d' j ≠ 0) :
    (pfPoly x r d').eval s =
      (∏ j, (s - d' j)) * (s - x + ∑ j, r j / (s - d' j)) := by
  have hj : ∀ j, (∏ k ∈ univ.erase j, (s - d' k)) = (∏ k, (s - d' k)) / (s - d' j) := by
    intro j
    rw [eq_div_iff (hs j), mul_comm, Finset.mul_prod_erase univ (fun k => s - d' k) (mem_univ j)]
  simp only [pfPoly, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_prod, eval_finsetSum]
  rw [mul_add, Finset.mul_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hj j]
  ring

lemma prod_eq_pfPoly (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (h : Function.Injective (Sum.elim d d')) :
    (∏ i, (X - C (d i)) : ℝ[X]) = pfPoly (pfX d d') (pfR d d') d' := by
  have hdd' : ∀ i j, d i - d' j ≠ 0 := by
    intro i j hij
    have : Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j) := by
      simpa using sub_eq_zero.mp hij
    exact absurd (h this) (by simp)
  have hinj : Function.Injective d := fun a b hab => by
    have : Sum.elim d d' (Sum.inl a) = Sum.elim d d' (Sum.inl b) := by simpa using hab
    simpa using h this
  have hP : (∏ i, (X - C (d i)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hQ : (∏ j, (X - C (d' j)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPd : (∏ i, (X - C (d i)) : ℝ[X]).degree = (m + 1 : ℕ) := by
    rw [degree_eq_natDegree hP.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  have hQd : (∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  have hL : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).Monic := (monic_X_sub_C _).mul hQ
  have hLd : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).degree = (m + 1 : ℕ) := by
    rw [degree_eq_natDegree hL.ne_zero, (monic_X_sub_C _).natDegree_mul hQ, hQd]
    simp [add_comm]
  have hsub : ((∏ i, (X - C (d i)) : ℝ[X]) -
      (X - C (pfX d d')) * ∏ j, (X - C (d' j))).degree < ((m + 1 : ℕ) : WithBot ℕ) := by
    have := degree_sub_lt (hPd.trans hLd.symm) hP.ne_zero (hP.leadingCoeff.trans hL.leadingCoeff.symm)
    rwa [hPd] at this
  have hterm : ∀ j : Fin m, (C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < ((m + 1 : ℕ) : WithBot ℕ) := by
    intro j
    rw [← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ?_
    have hM : (∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).Monic :=
      monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
    rw [degree_eq_natDegree hM.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
    exact_mod_cast (by omega : m - 1 < m + 1)
  have hsum : (∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < ((m + 1 : ℕ) : WithBot ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => hterm j
  have hdeg : ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d').degree
      < (univ : Finset (Fin (m + 1))).card := by
    have : ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d') =
        ((∏ i, (X - C (d i)) : ℝ[X]) - (X - C (pfX d d')) * ∏ j, (X - C (d' j))) -
          ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) := by
      simp only [pfPoly]; ring
    rw [this]
    simpa using (degree_sub_le _ _).trans_lt (max_lt hsub hsum)
  refine sub_eq_zero.mp (eq_zero_of_degree_lt_of_eval_index_eq_zero univ hinj.injOn hdeg ?_)
  intro i _
  have hz := GlobalTheory.T.partial_fraction_diagonal_identity d d' h i
  rw [eval_sub, eval_pfPoly _ _ _ _ (hdd' i), hz, mul_zero, eval_prod]
  simp only [eval_sub, eval_X, eval_C, sub_zero]
  exact Finset.prod_eq_zero (mem_univ i) (sub_self _)

theorem pfDer : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ),
    Function.Injective (Sum.elim d d') →
      ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  intro m d d' h i
  have hdd' : ∀ j, d i - d' j ≠ 0 := by
    intro j hij
    have : Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j) := by
      simpa using sub_eq_zero.mp hij
    exact absurd (h this) (by simp)
  set Q : ℝ[X] := ∏ j, (X - C (d' j)) with hQdef
  have hQe : ∀ s, Q.eval s = ∏ j, (s - d' j) := fun s => by simp [hQdef, eval_prod]
  have hQ0 : Q.eval (d i) ≠ 0 := by
    rw [hQe]; exact Finset.prod_ne_zero_iff.2 fun j _ => hdd' j

  let f : ℝ → ℝ := fun s => s - pfX d d' + ∑ j, pfR d d' j / (s - d' j)
  have hterm : ∀ j ∈ (univ : Finset (Fin m)), HasDerivAt (fun s => pfR d d' j / (s - d' j))
      (-(pfR d d' j / (d i - d' j) ^ 2)) (d i) := by
    intro j _
    have h1 : HasDerivAt (fun s : ℝ => s - d' j) 1 (d i) := (hasDerivAt_id _).sub_const _
    have h2 := (hasDerivAt_const (d i) (pfR d d' j)).fun_div h1 (hdd' j)
    exact h2.congr_deriv (by simp [neg_div])
  have hf : HasDerivAt f (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2) (d i) := by
    have h3 := HasDerivAt.fun_sum hterm
    have h4 := ((hasDerivAt_id (d i)).sub_const (pfX d d')).fun_add h3
    exact h4.congr_deriv (by simp [sub_eq_add_neg])
  have hf0 : f (d i) = 0 := GlobalTheory.T.partial_fraction_diagonal_identity d d' h i
  have hprod : HasDerivAt (fun s => Q.eval s * f s)
      (Q.eval (d i) * (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2)) (d i) := by
    have := (Q.hasDerivAt (d i)).fun_mul hf
    exact this.congr_deriv (by simp [hf0])

  set P : ℝ[X] := ∏ k, (X - C (d k)) with hPdef
  have hPfac : P = (X - C (d i)) * ∏ k ∈ univ.erase i, (X - C (d k)) :=
    (Finset.mul_prod_erase univ (fun k => (X - C (d k) : ℝ[X])) (mem_univ i)).symm
  have hPder : P.derivative.eval (d i) = ∏ k ∈ univ.erase i, (d i - d k) := by
    rw [hPfac, derivative_mul]
    simp [eval_prod]
  have hev : (fun s => P.eval s) =ᶠ[nhds (d i)] fun s => Q.eval s * f s := by
    have hopen : ∀ᶠ s in nhds (d i), ∀ j, s - d' j ≠ 0 := by
      refine Filter.eventually_all.2 fun j => ?_
      have hc : ContinuousAt (fun s : ℝ => s - d' j) (d i) := by fun_prop
      exact hc.eventually_ne (hdd' j)
    filter_upwards [hopen] with s hs
    rw [hPdef, prod_eq_pfPoly d d' h, eval_pfPoly _ _ _ _ hs, hQe]
  have huniq := (P.hasDerivAt (d i)).unique (hprod.congr_of_eventuallyEq hev)
  rw [hPder] at huniq
  unfold pfD
  rw [← hQe (d i), huniq]
  field_simp

end GlobalTheory.CompanionTheory.RgHeFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiCongrRightSingle
section
open TensorProduct CrystallineSemistableComparison.Onto

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.OmKun

theorem piCongrRight_single {K ι : Type} [CommRing K] [DecidableEq ι] {X Y : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)]
    (f : ∀ i, X i ≃ₗ[K] Y i) (a : ι) (x : X a) :
    LinearEquiv.piCongrRight f (Pi.single a x) = Pi.single a (f a x) := by
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem omKun_pushout (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R] (c : ℕ) :
    ∃ e : (∀ a : Fin (c + 1), TensorProduct K (Om K A a) (Om K B (c - a))) ≃ₗ[K] Om K R c,
      ∀ (a : Fin (c + 1)) (g₀ : A) (g : Fin a → A) (h₀ : B) (h : Fin (c - a) → B),
        e (Pi.single a (form K g₀ g ⊗ₜ form K h₀ h)) = form K (algebraMap A R g₀ * algebraMap B R h₀)
          (Fin.append (fun k => algebraMap A R (g k)) (fun k => algebraMap B R (h k)) ∘
            Fin.cast (by have := a.2; omega)) := by
  obtain ⟨r, π, h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.KaehlerPushout.kaehler_pushout_split K A B R
  obtain ⟨E, hE⟩ := GlobalTheory.CompanionTheory.TopExtSplit.exteriorPower_split R _ _ _ _ _ r π h1 h2 h3 h4 h5 c
  choose bA hbA using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv A R (Ω[A⁄K]) a
  choose bB hbB using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv B R (Ω[B⁄K]) a
  choose t ht using fun a : Fin (c + 1) => GlobalTheory.CompanionTheory.TensorPushout.tensor_equiv_baseChange_tensor K A B R (Om K A a) (Om K B (c - a))
  refine ⟨LinearEquiv.piCongrRight (fun a => t a ≪≫ₗ
    (TensorProduct.congr (bA a) (bB (c - a))).restrictScalars K) ≪≫ₗ E.restrictScalars K, ?_⟩
  intro a g₀ g h₀ h
  have hA : bA a ((1 : R) ⊗ₜ[A] form K g₀ g) = algebraMap A R g₀ •
      exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbA, Algebra.smul_def, mul_one]
  have hB : bB (c - a) ((1 : R) ⊗ₜ[B] form K h₀ h) = algebraMap B R h₀ •
      exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbB, Algebra.smul_def, mul_one]
  have hmain : (TensorProduct.congr (bA a) (bB (c - a))) (((1 : R) ⊗ₜ[A] form K g₀ g) ⊗ₜ[R]
      ((1 : R) ⊗ₜ[B] form K h₀ h)) = (algebraMap A R g₀ * algebraMap B R h₀) •
        (exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) ⊗ₜ[R]
        exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k))) := by
    rw [TensorProduct.congr_tmul, hA, hB, TensorProduct.smul_tmul_smul]
  simp only [LinearEquiv.trans_apply, piCongrRight_single, LinearEquiv.restrictScalars_apply, ht,
    hmain, Pi.single_smul, map_smul, hE]
  unfold form
  congr 2
  funext k
  simp only [Function.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]
  generalize Fin.cast _ k = j
  induction j using Fin.addCases with
  | left j => simp [KaehlerDifferential.mapBaseChange_tmul]
  | right j => simp [KaehlerDifferential.mapBaseChange_tmul]

theorem omKun : CrystallineSemistableComparison.Onto.OmKun := by
  intro K A B _ _ _ _ _ c
  let _ : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower K B (A ⊗[K] B) := Algebra.TensorProduct.right_isScalarTower
  obtain ⟨e, he⟩ := omKun_pushout K A B (A ⊗[K] B) c
  refine ⟨e, fun a g₀ g h₀ h => ?_⟩
  rw [he]
  congr 1
  change g₀ ⊗ₜ[K] (1 : B) * (1 : A) ⊗ₜ[K] h₀ = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.CompanionTheory.OmKun
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatProdSpanTensors
section
open Classical MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.FrobProd

theorem exists_compact_clopen {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] {x : X} {u : Set X} (hu : IsOpen u) (hx : x ∈ u) :
    ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ u := by
  obtain ⟨K, hK, hxK, hKu⟩ := exists_compact_subset hu hx
  obtain ⟨V, hV, hxV, hVK⟩ := (isTopologicalBasis_isClopen (X := X)).exists_subset_of_mem_open
    hxK isOpen_interior
  have hVK' : V ⊆ K := hVK.trans interior_subset
  exact ⟨V, hK.of_isClosed_subset hV.isClosed hVK', hV, hxV, hVK'.trans hKu⟩


open Classical in
theorem fiber_ind_mem {X S : Type} [TopologicalSpace X] [T2Space X] {ξ : X → S}
    (hξ : IsLocallyConstant ξ) (s : S) (hs : IsCompact (ξ ⁻¹' {s})) :
    (fun x => if ξ x = s then (1 : ℂ) else 0) ∈ SB X := by
  refine mem_SB_iff.2 ⟨hξ.comp (fun t => if t = s then (1 : ℂ) else 0), ?_⟩
  refine HasCompactSupport.intro hs fun x hx => ?_
  have : ξ x ≠ s := hx
  simp [this]


open Classical in
theorem isLocallyConstant_pattern {X ι : Type} [TopologicalSpace X] [Fintype ι] {U : ι → Set X}
    (hU : ∀ i, IsClopen (U i)) :
    IsLocallyConstant (fun x => Finset.univ.filter (fun i => x ∈ U i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h : ∀ᶠ y in nhds x, ∀ i, (y ∈ U i ↔ x ∈ U i) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hx : x ∈ U i
    · filter_upwards [(hU i).isOpen.mem_nhds hx] with y hy
      exact iff_of_true hy hx
    · filter_upwards [(hU i).compl.isOpen.mem_nhds hx] with y hy
      exact iff_of_false hy hx
  filter_upwards [h] with y hy
  ext i
  simp [hy i]


open Classical in
theorem isCompact_pattern_fiber {X ι : Type} [TopologicalSpace X] [T2Space X] [Fintype ι]
    {U : ι → Set X} (hU : ∀ i, IsClopen (U i)) (hc : ∀ i, IsCompact (U i)) (s : Finset ι)
    (hs : s ≠ ∅) :
    IsCompact ((fun x => Finset.univ.filter (fun i => x ∈ U i)) ⁻¹' {s}) := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hs
  refine (hc i).of_isClosed_subset ((isLocallyConstant_pattern hU).isClosed_fiber s) ?_
  intro x hx
  have hx' : Finset.univ.filter (fun i => x ∈ U i) = s := hx
  rw [← hx'] at hi
  simpa using hi


open Classical in
theorem span_of_factor {A B S T : Type} [TopologicalSpace A] [T2Space A] [TopologicalSpace B]
    [T2Space B] [Fintype S] [Fintype T] {ξ : A → S} {η : B → T}
    (hξ : IsLocallyConstant ξ) (hη : IsLocallyConstant η) (s0 : S) (t0 : T)
    (hcs : ∀ s, s ≠ s0 → IsCompact (ξ ⁻¹' {s})) (hct : ∀ t, t ≠ t0 → IsCompact (η ⁻¹' {t}))
    (f : SB (A × B))
    (hΦ : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 →
      (f : A × B → ℂ) q = (f : A × B → ℂ) q')
    (h0 : ∀ q : A × B, ξ q.1 = s0 → (f : A × B → ℂ) q = 0)
    (h0' : ∀ q : A × B, η q.2 = t0 → (f : A × B → ℂ) q = 0) :
    (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B,
      (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧
        F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  have hsum : (f : A × B → ℂ) =
      ∑ p : S × T, fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0 := by
    funext q
    rw [Finset.sum_apply, Finset.sum_eq_single (ξ q.1, η q.2)]
    · simp
    · intro p _ hp
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hp (Prod.ext h1.symm h2.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine Eq.mpr (congrArg (· ∈ _) hsum) (Submodule.sum_mem _ fun p _ => ?_)
  by_cases hex : ∃ q0 : A × B, ξ q0.1 = p.1 ∧ η q0.2 = p.2 ∧ (f : A × B → ℂ) q0 ≠ 0
  · obtain ⟨q0, h1, h2, h3⟩ := hex
    have hs : p.1 ≠ s0 := fun h => h3 (h0 q0 (h1.trans h))
    have ht : p.2 ≠ t0 := fun h => h3 (h0' q0 (h2.trans h))
    let ia : SB A := ⟨_, fiber_ind_mem hξ p.1 (hcs _ hs)⟩
    let ib : SB B := ⟨_, fiber_ind_mem hη p.2 (hct _ ht)⟩
    have hia : ∀ x, (ia : A → ℂ) x = if ξ x = p.1 then 1 else 0 := fun _ => rfl
    have hib : ∀ x, (ib : B → ℂ) x = if η x = p.2 then 1 else 0 := fun _ => rfl
    refine Submodule.subset_span ⟨(f : A × B → ℂ) q0 • ia, ib, ?_, ?_⟩
    · intro q ha hb
      have e1 : ξ q.1 = p.1 := by
        by_contra h
        apply ha
        simp [hia, h]
      have e2 : η q.2 = p.2 := by
        by_contra h
        apply hb
        simp [hib, h]
      rw [hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]
      exact h3
    · funext q
      by_cases e1 : ξ q.1 = p.1
      · by_cases e2 : η q.2 = p.2
        · simp [hia, hib, e1, e2, hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]
        · simp [hia, hib, e2]
      · simp [hia, e1]
  · have hz : (fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0) = 0 := by
      funext q
      by_cases e : ξ q.1 = p.1 ∧ η q.2 = p.2
      · rw [if_pos e]
        by_contra h
        exact hex ⟨q, e.1, e.2, h⟩
      · rw [if_neg e]
        rfl
    rw [hz]
    exact Submodule.zero_mem _


open Classical in
theorem span_box : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] (f : SB (A × B)), (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B, (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧ F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  intro A B _ _ _ _ _ _ _ _ f
  have hlc : IsLocallyConstant (f : A × B → ℂ) := (mem_SB_iff.1 f.2).1
  have hcs : HasCompactSupport (f : A × B → ℂ) := (mem_SB_iff.1 f.2).2
  have hbox : ∀ q : A × B, ∃ U : Set A, ∃ V : Set B, IsCompact U ∧ IsClopen U ∧ IsCompact V ∧
      IsClopen V ∧ q.1 ∈ U ∧ q.2 ∈ V ∧
      ∀ q' : A × B, q'.1 ∈ U → q'.2 ∈ V → (f : A × B → ℂ) q' = (f : A × B → ℂ) q := by
    intro q
    obtain ⟨u, v, hu, hv, hqu, hqv, huv⟩ := isOpen_prod_iff.1
      (hlc.isOpen_fiber ((f : A × B → ℂ) q)) q.1 q.2 rfl
    obtain ⟨U, hUc, hUo, hqU, hUu⟩ := exists_compact_clopen hu hqu
    obtain ⟨V, hVc, hVo, hqV, hVv⟩ := exists_compact_clopen hv hqv
    exact ⟨U, V, hUc, hUo, hVc, hVo, hqU, hqV, fun q' h1 h2 => huv ⟨hUu h1, hVv h2⟩⟩
  choose U V hUc hUo hVc hVo hqU hqV hUV using hbox
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover (fun q => U q ×ˢ V q)
    (fun q _ => ((hUo q).isOpen.prod (hVo q).isOpen).mem_nhds ⟨hqU q, hqV q⟩)
  have hcov : ∀ q : A × B, (f : A × B → ℂ) q ≠ 0 → ∃ i : t, q.1 ∈ U i ∧ q.2 ∈ V i := by
    intro q hq
    have := ht (subset_tsupport _ hq)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h.1, h.2⟩
  let ξ : A → Finset t := fun x => Finset.univ.filter (fun i : t => x ∈ U i)
  let η : B → Finset t := fun x => Finset.univ.filter (fun i : t => x ∈ V i)
  have hξm : ∀ x i, i ∈ ξ x ↔ x ∈ U i := fun x i => by simp [ξ]
  have hηm : ∀ x i, i ∈ η x ↔ x ∈ V i := fun x i => by simp [η]
  have hstep : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 → (f : A × B → ℂ) q ≠ 0 →
      (f : A × B → ℂ) q = (f : A × B → ℂ) q' := by
    intro q q' e1 e2 hq
    obtain ⟨i, h1, h2⟩ := hcov q hq
    have h1' : q'.1 ∈ U i := (hξm _ _).1 (e1 ▸ (hξm _ _).2 h1)
    have h2' : q'.2 ∈ V i := (hηm _ _).1 (e2 ▸ (hηm _ _).2 h2)
    rw [hUV i q h1 h2, hUV i q' h1' h2']
  refine span_of_factor (ξ := ξ) (η := η)
    (isLocallyConstant_pattern (U := fun i : t => U i) fun i => hUo i)
    (isLocallyConstant_pattern (U := fun i : t => V i) fun i => hVo i) ∅ ∅
    (fun s hs => isCompact_pattern_fiber (U := fun i : t => U i) (fun i => hUo i) (fun i => hUc i) s hs)
    (fun s hs => isCompact_pattern_fiber (U := fun i : t => V i) (fun i => hVo i) (fun i => hVc i) s hs)
    f ?_ ?_ ?_
  · intro q q' e1 e2
    by_cases hq : (f : A × B → ℂ) q = 0
    · by_cases hq' : (f : A × B → ℂ) q' = 0
      · rw [hq, hq']
      · exact (hstep q' q e1.symm e2.symm hq').symm
    · exact hstep q q' e1 e2 hq
  · intro q hq
    by_contra h
    obtain ⟨i, h1, -⟩ := hcov q h
    have : i ∈ ξ q.1 := (hξm _ _).2 h1
    rw [hq] at this
    simp at this
  · intro q hq
    by_contra h
    obtain ⟨i, -, h2⟩ := hcov q h
    have : i ∈ η q.2 := (hηm _ _).2 h2
    rw [hq] at this
    simp at this

end GlobalTheory.CompanionTheory.FrobProd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzQuadraticPhaseMultiplication
section
open scoped Matrix SchwartzMap ComplexConjugate

namespace GlobalTheory.CompanionTheory.QuadChirp

theorem ofReal_re_trace {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (((Matrix.trace (b * (Aᴴ * A))).re : ℝ) : ℂ) = Matrix.trace (b * (Aᴴ * A)) := by
  have h : (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = Matrix.trace (b * (Aᴴ * A)) := by
    rw [show (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = star (Matrix.trace (b * (Aᴴ * A))) from rfl,
      ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hb, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.1 h

theorem coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u l i) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth

theorem conj_coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u l i)) :=
  ((Complex.conjCLE.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth

theorem trace_hasTemperateGrowth {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) :
    Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) := by
  have heq : (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) =
      fun u => ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m, b i j * (star (u l j) * u l i) := by
    funext u
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Finset.mul_sum]
  rw [heq]
  refine Function.HasTemperateGrowth.sum fun i _ => Function.HasTemperateGrowth.sum fun j _ =>
    Function.HasTemperateGrowth.sum fun l _ => ?_
  exact (Function.HasTemperateGrowth.const (b i j)).mul
    ((GlobalTheory.CompanionTheory.QuadChirp.conj_coord_hasTemperateGrowth l j).mul (GlobalTheory.CompanionTheory.QuadChirp.coord_hasTemperateGrowth l i))

theorem chirp_hasTemperateGrowth {m n : ℕ} (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
        Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) := by
  have hre : Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      k * (Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))).re) :=
    (Function.HasTemperateGrowth.const k).mul
      (Complex.reCLM.hasTemperateGrowth.comp (GlobalTheory.CompanionTheory.QuadChirp.trace_hasTemperateGrowth b))
  have hcomp := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hre
  convert hcomp using 1
  funext u
  rw [Function.comp_apply, GlobalTheory.Published.Metaplectic.eChar_apply]
  congr 1
  have hT := GlobalTheory.CompanionTheory.QuadChirp.ofReal_re_trace b hb (Matrix.of u)
  rw [Complex.ofReal_mul]
  conv_lhs => rw [← hT]
  ring

theorem exists_schwartz_chirp_mul :
    ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b →
      ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
        ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
          Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by
  intro m n k b hb φ
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi *
    Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) φ, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.QuadChirp.chirp_hasTemperateGrowth k b hb), smul_eq_mul]

end GlobalTheory.CompanionTheory.QuadChirp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDualFamilyHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_dual_family_holds : PositivityTheory.Rg.Tf.Loc.IntegralBasisUnramified → PositivityTheory.Rg.Tf.Loc.TraceOneIntegralElement := by
  first | exact @GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family | exact GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family | (intros; apply GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family <;> assumption)
end

