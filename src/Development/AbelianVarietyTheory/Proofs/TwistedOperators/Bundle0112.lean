module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompat
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.RealPar

theorem flow_pair_mem_range {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : E →ₗ[ℂ] H₁) (j₂ : E →ₗ[ℂ] H₂) (a : E →ₗ[ℂ] E)
    (U₁ : ℝ → H₁ →L[ℂ] H₁) (U₂ : ℝ → H₂ →L[ℂ] H₂) (h₁ : U₁ 0 = 1) (h₂ : U₂ 0 = 1)
    (a₁ : ∀ s t, U₁ (s + t) = U₁ s * U₁ t) (a₂ : ∀ s t, U₂ (s + t) = U₂ s * U₂ t)
    (d₁ : ∀ v, HasDerivAt (fun t : ℝ => U₁ t (j₁ v)) (j₁ (a v)) 0)
    (d₂ : ∀ v, HasDerivAt (fun t : ℝ => U₂ t (j₂ v)) (j₂ (a v)) 0) (t : ℝ) (w : E) :
    ∃ w' : E, U₁ t (j₁ w) = j₁ w' ∧ U₂ t (j₂ w) = j₂ w' := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂
  let ι : E →ₗ[ℂ] WithLp 2 (H₁ × H₂) := e.symm.toLinearEquiv.toLinearMap ∘ₗ j₁.prod j₂
  let U : ℝ → WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) := fun s =>
    (e.symm : H₁ × H₂ →L[ℂ] WithLp 2 (H₁ × H₂)) ∘L ((U₁ s).prodMap (U₂ s)) ∘L
      (e : WithLp 2 (H₁ × H₂) →L[ℂ] H₁ × H₂)
  have hU : ∀ s x, U s x = e.symm (U₁ s (e x).1, U₂ s (e x).2) := fun s x => rfl
  have hι : ∀ v, ι v = e.symm (j₁ v, j₂ v) := fun v => rfl
  have key := flow_mem_map ι a ⊤ (fun _ _ => trivial) U
    (by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [hU, h₁, h₂]
      exact e.symm_apply_apply x)
    (fun s r => by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [ContinuousLinearMap.mul_apply, hU, hU, hU, a₁, a₂, e.apply_symm_apply]
      rfl)
    (fun v => by
      have h := ((e.symm : H₁ × H₂ →L[ℂ] WithLp 2 (H₁ × H₂)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) ((d₁ v).prodMk (d₂ v))
      exact h) t (ι w) ⟨w, trivial, rfl⟩
  obtain ⟨w', -, hw'⟩ := key
  rw [hU, hι, hι, e.apply_symm_apply] at hw'
  have h := e.symm.injective hw'
  exact ⟨w', (congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

theorem pair_kEquivariant_of_lie : ∀ (p q : ℕ) (T : GrpData p q), (∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y})) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (a : Mat p q → E →ₗ[ℂ] E) (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, IsKC Y → ∀ w, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ w)) (j₁ (a Y w)) 0 ∧ HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ w)) (j₂ (a Y w)) 0) → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') := by
  intro p q T hgen π₁ π₂ E _ _ _ a j₁ j₂ hder k hk
  have hflow : ∀ Y ∈ upq p q, IsKC Y → ∀ (t : ℝ) (w : E), ∃ w' : E,
      π₁.π (T.expt (t • Y)) (j₁ w) = j₁ w' ∧ π₂.π (T.expt (t • Y)) (j₂ w) = j₂ w' := by
    intro Y hY hK t w
    exact flow_pair_mem_range j₁ j₂ (a Y) (fun t => π₁.π (T.expt (t • Y))) (fun t => π₂.π (T.expt (t • Y)))
      (by simp [T.expt_zero]) (by simp [T.expt_zero])
      (fun s t => by simp only [T.expt_add Y hY, map_mul])
      (fun s t => by simp only [T.expt_add Y hY, map_mul])
      (fun v => (hder Y hY hK v).1) (fun v => (hder Y hY hK v).2) t w
  refine Subgroup.closure_induction'' (p := fun k _ => ∀ w : E, ∃ w' : E,
    π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') ?_ ?_ ?_ ?_ (hgen k hk)
  · rintro _ ⟨Y, ⟨hY, hK⟩, rfl⟩ w
    simpa using hflow Y hY hK 1 w
  · rintro _ ⟨Y, ⟨hY, hK⟩, rfl⟩ w
    have h : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have := T.expt_add Y hY (-1) 1
      rw [neg_add_cancel, zero_smul, one_smul, T.expt_zero] at this
      exact (eq_inv_of_mul_eq_one_left this.symm).symm
    rw [h]
    exact hflow Y hY hK (-1) w
  · intro w
    exact ⟨w, by simp, by simp⟩
  · intro x y _ _ hx hy w
    obtain ⟨w', h1, h2⟩ := hy w
    obtain ⟨w'', h3, h4⟩ := hx w'
    exact ⟨w'', by rw [map_mul, ContinuousLinearMap.mul_apply, h1, h3],
      by rw [map_mul, ContinuousLinearMap.mul_apply, h2, h4]⟩

end GlobalTheory.RealPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjParahoric
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParahoricConjugateOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_conj_inf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (g : G) :
    IsOpen ((H.map (MulAut.conj g).toMonoidHom ⊓ H : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  refine IsOpen.inter ?_ hH
  have : ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  rw [this]
  exact hH.preimage (by fun_prop)

theorem isOpen_KO (n : Type) [Fintype n] [DecidableEq n] : IsOpen (KO k n : Set (GL n k)) :=
  Subgroup.isOpen_mono StepData.KOne_le_KO StepData.isOpen_KOne

theorem isOpen_parahoric (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] :
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  refine Subgroup.isOpen_mono (H₁ := KOne k (A ⊕ D)) (fun g hg => ?_) StepData.isOpen_KOne
  refine mem_parahoric.2 ⟨StepData.KOne_le_KO hg, fun i j => ?_⟩
  simpa using StepData.mem_KOne.1 hg (.inr i) (.inl j)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem torusElt_zero (n : Type) [Fintype n] [DecidableEq n] (ϖ : kˣ) :
    torusElt k n ϖ (fun _ => 0) = 1 := by
  refine Units.ext ?_
  rw [val_torusElt]
  simp

theorem conj_one_inf {G : Type} [Group G] (H : Subgroup G) :
    (H.map (MulAut.conj (1 : G)).toMonoidHom ⊓ H : Subgroup G) = H := by
  have : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.map_id, inf_idem]

theorem vol_conj_inf [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ)
    (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    (volM ν (A ⊕ D) (A ⊕ D) (Units.val ''
      (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)))).toReal =
      (volM ν A A (Units.val '' (KO k A : Set (GL A k)))).toReal *
        (ν (𝒪[k] : Set k)).toReal ^ (2 * (Fintype.card A * Fintype.card D)) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) *
        (volM ν D D (Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k)))).toReal := by
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  have h1 := _root_.GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ A D (fun _ j => max 0 (-e j))
  have h2 := _root_.GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ D A (fun i _ => 1 + max 0 (e i))
  rw [GlobalTheory.T.val_twoBlockParahoric_inf_torusConj_blockwise k ϖ hϖ A D e, _root_.GlobalTheory.blockVolume_prod, h1, h2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (zpow_pos hq _).le]
  have hs : -((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e)) =
      (-∑ _i : A, ∑ j : D, max 0 (-e j)) + (-∑ i : D, ∑ _j : A, (1 + max 0 (e i))) := by
    have : sumAbs e = ∑ j : D, max 0 (-e j) + ∑ j : D, max 0 (e j) := by
      rw [sumAbs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases le_total 0 (e j) with h | h
      · rw [abs_of_nonneg h, max_eq_left (by omega), max_eq_right h]; ring
      · rw [abs_of_nonpos h, max_eq_right (by omega), max_eq_left h]; ring
    rw [this, Finset.sum_comm (s := (Finset.univ : Finset D))]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib]
    ring
  rw [hs, zpow_add₀ hq.ne', mul_comm (Fintype.card D) (Fintype.card A)]
  ring

theorem relIndex_conj_parahoric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    ((((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℕ) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        ((((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℕ) : ℝ) := by
  borelize k
  let ν : Measure k := Measure.addHaar
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  obtain ⟨hp, hJ⟩ := _root_.GlobalTheory.IndexVolume.relIndex_mul_volM k ν (A ⊕ D) _ (parahoric k A D) inf_le_right
    (fun g hg => (mem_parahoric.1 hg).1) (isOpen_conj_inf _ (isOpen_parahoric A D) (mtor (A := A) ϖ e))
  obtain ⟨-, hK⟩ := _root_.GlobalTheory.IndexVolume.relIndex_mul_volM k ν D _ (KO k D) inf_le_right le_rfl
    (isOpen_conj_inf _ (isOpen_KO D) (torusElt k D ϖ e))
  rw [Subgroup.inf_relIndex_right] at hJ hK
  have h0 := vol_conj_inf ν ϖ hϖ A D (fun _ => 0)
  have hm : mtor (A := A) ϖ (fun _ : D => 0) = 1 := by
    rw [← torusElt_zero (A ⊕ D) ϖ, mtor]
    congr 1
    funext x
    cases x <;> rfl
  rw [hm, torusElt_zero, conj_one_inf, conj_one_inf] at h0
  refine mul_right_cancel₀ hp.ne' ?_
  rw [hJ, h0, ← hK, vol_conj_inf ν ϖ hϖ A D e]
  have hs : sumAbs (fun _ : D => (0 : ℤ)) = 0 := by simp [sumAbs]
  have hz : (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs (fun _ : D => (0 : ℤ))))) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) := by
    rw [← zpow_add₀ hq.ne', hs]
    congr 1
    ring
  rw [hz]
  ring

end GlobalTheory.ParahoricConjugateOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobBdSeminorm
section
noncomputable section

open Formalism.L2.Theta Formalism.MainNotions.S GlobalTheory.SmoothGlob

namespace GlobalTheory.FactorExtension

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sobNorm_nonneg (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (w : H) : 0 ≤ sobNorm σ S w :=
  List.sum_nonneg fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _

theorem sobNorm_append (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (w : H) : sobNorm σ (S ++ S') w = sobNorm σ S w + sobNorm σ S' w := by
  simp [sobNorm, List.map_append, List.sum_append]

theorem sob_max {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S S' : List (List (Matrix (Fin n) (Fin n) ℂ))}
    {C C' a a' : ℝ} {w : H} (h : a ≤ C * sobNorm σ S w) (h' : a' ≤ C' * sobNorm σ S' w) :
    a + a' ≤ max |C| |C'| * sobNorm σ (S ++ S') w ∧ max a a' ≤ max |C| |C'| * sobNorm σ (S ++ S') w := by
  have h0 := sobNorm_nonneg σ S w
  have h0' := sobNorm_nonneg σ S' w
  have e1 : C * sobNorm σ S w ≤ max |C| |C'| * sobNorm σ S w :=
    mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_max_left _ _)) h0
  have e2 : C' * sobNorm σ S' w ≤ max |C| |C'| * sobNorm σ S' w :=
    mul_le_mul_of_nonneg_right ((le_abs_self C').trans (le_max_right _ _)) h0'
  have hm : 0 ≤ max |C| |C'| := (abs_nonneg C).trans (le_max_left _ _)
  rw [sobNorm_append, mul_add]
  refine ⟨by linarith, max_le ?_ ?_⟩
  · nlinarith [mul_nonneg hm h0']
  · nlinarith [mul_nonneg hm h0]

variable {E : Type} [AddCommGroup E] [Module ℂ E]

def sobBd (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : ℕ → Seminorm ℂ E) :
    Submodule ℂ (H →ₗ[ℂ] E) where
  carrier := {L | ∀ i, ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧
      ∀ w, SmoothVec (lieSet ε) σ w → p i (L w) ≤ C * sobNorm σ S w}
  zero_mem' := fun i => ⟨[], 0, by simp, fun w _ => by simp⟩
  add_mem' := by
    intro L L' hL hL' i
    obtain ⟨S, C, hS, h⟩ := hL i
    obtain ⟨S', C', hS', h'⟩ := hL' i
    refine ⟨S ++ S', max |C| |C'|, fun l hl => ?_, fun w hw => ?_⟩
    · rcases List.mem_append.1 hl with hl | hl
      · exact hS l hl
      · exact hS' l hl
    · exact (map_add_le_add (p i) _ _).trans (sob_max (h w hw) (h' w hw)).1
  smul_mem' := by
    intro c L hL i
    obtain ⟨S, C, hS, h⟩ := hL i
    refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
    rw [LinearMap.smul_apply, map_smul_eq_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h w hw) (norm_nonneg c)

theorem sobBd_congr {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : ℕ → Seminorm ℂ E}
    {L L' : H →ₗ[ℂ] E} (hL : L ∈ sobBd ε σ p) (h : ∀ w, SmoothVec (lieSet ε) σ w → L' w = L w) :
    L' ∈ sobBd ε σ p := fun i => by
  obtain ⟨S, C, hS, hb⟩ := hL i
  exact ⟨S, C, hS, fun w hw => by rw [h w hw]; exact hb w hw⟩

theorem sobBd_seminorm [TopologicalSpace E] {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) {L : H →ₗ[ℂ] E} (hL : L ∈ sobBd ε σ p) (q : Seminorm ℂ E)
    (hq : Continuous q) : ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧
      ∀ w, SmoothVec (lieSet ε) σ w → q (L w) ≤ C * sobNorm σ S w := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hp q hq
  have key : ∀ t : Finset ℕ, ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ),
      (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧ ∀ w, SmoothVec (lieSet ε) σ w → (t.sup p) (L w) ≤ C * sobNorm σ S w := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨[], 0, by simp, fun w _ => by simp⟩
    | insert i t _ ih =>
      obtain ⟨S, C, hS, h⟩ := ih
      obtain ⟨S', C', hS', h'⟩ := hL i
      refine ⟨S' ++ S, max |C'| |C|, fun l hl => ?_, fun w hw => ?_⟩
      · rcases List.mem_append.1 hl with hl | hl
        · exact hS' l hl
        · exact hS l hl
      · rw [Finset.sup_insert, Seminorm.sup_apply]
        exact (sob_max (h' w hw) (h w hw)).2
  obtain ⟨S, C', hS, h⟩ := key s
  refine ⟨S, C * C', hS, fun w hw => ?_⟩
  calc q (L w) ≤ (C • s.sup p) (L w) := hC _
    _ = C * (s.sup p) (L w) := rfl
    _ ≤ C * (C' * sobNorm σ S w) := mul_le_mul_of_nonneg_left (h w hw) C.2
    _ = C * C' * sobNorm σ S w := by ring

theorem sobBd_comp [TopologicalSpace E] [IsTopologicalAddGroup E] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) {L : H →ₗ[ℂ] E}
    (hL : L ∈ sobBd ε σ p) (e : E →L[ℂ] E) : (e : E →ₗ[ℂ] E) ∘ₗ L ∈ sobBd ε σ p := fun i =>
  sobBd_seminorm hp hL ((p i).comp (e : E →ₗ[ℂ] E))
    ((hp.continuous_seminorm i).comp e.continuous)

theorem dRep_comm [TopologicalSpace E] [T2Space E] {ε : Fin n → Bool} {p : ℕ → Seminorm ℂ E}
    {π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)} (h : IsSmoothModRep ε p π dπ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) (e : E →L[ℂ] E)
    (he : ∀ t : ℝ, e.comp (π (NormedSpace.exp (t • X))) = (π (NormedSpace.exp (t • X))).comp e) :
    e.comp (dπ X) = (dπ X).comp e := by
  ext v
  have h1 := h.hasDRep X hX (e v)
  have h0 := h.hasDRep X hX v
  unfold HasDRep at h1 h0
  have h2 := (e.continuous.tendsto _).comp h0
  have h3 : Filter.Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (π (NormedSpace.exp (t • X)) (e v) - e v))
      (nhdsWithin 0 {0}ᶜ) (nhds (e (dπ X v))) := by
    refine h2.congr fun t => ?_
    have := congrArg (fun f : E →L[ℂ] E => f v) (he t)
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [Function.comp, map_smul, map_sub, this]
  exact tendsto_nhds_unique h3 h1

end GlobalTheory.FactorExtension

end
end

