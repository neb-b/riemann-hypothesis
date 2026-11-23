module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem isHomogeneous_multiset_prod_map {σ : Type*} (φ : ℕ → MvPolynomial σ ℤ)
    (hφ : ∀ b, (φ b).IsHomogeneous b) (t : Multiset ℕ) : ((t.map φ).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (hφ a).mul ih

theorem isHomogeneous_hsymm (N a : ℕ) : (hsymm (Fin N) ℤ a).IsHomogeneous a := by
  have h : ∀ t : Multiset (Fin N),
      ((t.map X).prod : MvPolynomial (Fin N) ℤ).IsHomogeneous (Multiset.card t) := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one (Fin N) ℤ
    | cons b t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
      exact (isHomogeneous_X ℤ b).mul ih
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  simpa [s.2] using h s.1

theorem FlagIndependence.proof (hExp : PairNumberExpansionIndependence.Statement)
    (hSeg : HsymmPairFlagIndependence.Statement) (hSym : SymmetricSpanHsymm.Statement) :
    FlagIndependence.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' v v' x x' u u' f g f₂ g₂
    hF1 hF2 m G hGm hGsym Gs Hs hGs hHs Q hQ
  classical

  have hvert : ∀ i, IsVerticalDivisor (pointIdeal O y) ϖ (Fin.append x u i - Fin.append x' u' i)
      (Fin.append f f₂ i) (Fin.append g g₂ i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact hF1.vertical i
    · simp only [Fin.append_right]
      exact hF2.vertical i
  have hind : ∀ (A : MvPolynomial (Fin (N + N)) ℤ) As Bs, A.IsHomogeneous m →
      IsPairExpansion m A As → IsPairExpansion m A Bs →
      pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
          (Fin.append g g₂) As Q =
        pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
          (Fin.append g g₂) Bs Q :=
    fun A As Bs hA h1 h2 => hExp O ϖ hϖ K ι _ d hV (N + N) _ _ _ _ hvert m A hA As Bs h1 h2 Q hQ

  let ex : MvPolynomial (Fin (N + N)) ℤ → Fin (N + N) → MvPolynomial (Fin (N + N) ⊕ Fin (N + N)) ℤ :=
    fun A => Classical.choose (exists_isPairExpansion (homogeneousComponent_isHomogeneous m A))
  have hex : ∀ A, IsPairExpansion m (homogeneousComponent m A) (ex A) :=
    fun A => Classical.choose_spec (exists_isPairExpansion (homogeneousComponent_isHomogeneous m A))
  let pn : MvPolynomial (Fin (N + N)) ℤ →+ ℤ := AddMonoidHom.mk'
    (fun A => pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
      (Fin.append g g₂) (ex A) Q)
    (by
      intro A B'
      have h2 : IsPairExpansion m (homogeneousComponent m (A + B')) (ex A + ex B') := by
        rw [map_add (f := _)]
        exact isPairExpansion_add (hex A) (hex B')
      rw [hind _ _ _ (homogeneousComponent_isHomogeneous m _) (hex (A + B')) h2]
      exact map_add (pairNumHom (pointIdeal O y) (Fin.append x u) (Fin.append x' u')
        (Fin.append f f₂) (Fin.append g g₂) Q) (ex A) (ex B'))
  have pn_eq : ∀ (A : MvPolynomial (Fin (N + N)) ℤ) As, A.IsHomogeneous m →
      IsPairExpansion m A As →
      pn A = pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
        (Fin.append g g₂) As Q := by
    intro A As hA h
    have h1 := hex A
    rw [homogeneousComponent_eq_self hA] at h1
    exact hind A _ _ hA h1 h

  have seg : ∀ (a r : ℕ) (R : MvPolynomial (Fin (N + N)) ℤ), R.IsHomogeneous r → a + r = m →
      pn (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) * R) =
        pn (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) * R) := by
    intro a r R hR har
    have hH : (hsymmTimes N (N + N) a R).IsHomogeneous (a + r) :=
      (isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR.rename_isHomogeneous
    obtain ⟨As, hAs⟩ := exists_isPairExpansion hH
    have key := hSeg O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' v v' x x' u u' f g f₂ g₂ hF1 hF2
      (N + N) _ _ _ _ hvert a r R hR As As hAs hAs Q (by rw [har]; exact hQ)
    let σx : Fin (N + (N + N)) → Fin (N + N) := Fin.append (Fin.castAdd N) id
    let σu : Fin (N + (N + N)) → Fin (N + N) := Fin.append (Fin.natAdd N) id
    have cx : ∀ {α : Type} (a₁ a₂ : Fin N → α),
        Fin.append a₁ a₂ ∘ σx = Fin.append a₁ (Fin.append a₁ a₂) := by
      intro α a₁ a₂
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [σx, Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
    have cu : ∀ {α : Type} (a₁ a₂ : Fin N → α),
        Fin.append a₁ a₂ ∘ σu = Fin.append a₂ (Fin.append a₁ a₂) := by
      intro α a₁ a₂
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [σu, Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
    have rx : rename σx (hsymmTimes N (N + N) a R) =
        rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) * R := by
      have e1 : σx ∘ Fin.castAdd (N + N) = Fin.castAdd N := by
        funext i
        simp only [σx, Function.comp_apply, Fin.append_left]
      have e2 : σx ∘ Fin.natAdd N = id := by
        funext i
        simp only [σx, Function.comp_apply, Fin.append_right, id_eq]
      simp only [hsymmTimes, map_mul, rename_rename, e1, e2, rename_id, AlgHom.id_apply]
    have ru : rename σu (hsymmTimes N (N + N) a R) =
        rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) * R := by
      have e1 : σu ∘ Fin.castAdd (N + N) = Fin.natAdd N := by
        funext i
        simp only [σu, Function.comp_apply, Fin.append_left]
      have e2 : σu ∘ Fin.natAdd N = id := by
        funext i
        simp only [σu, Function.comp_apply, Fin.append_right, id_eq]
      simp only [hsymmTimes, map_mul, rename_rename, e1, e2, rename_id, AlgHom.id_apply]
    have hpx := isPairExpansion_push σx hAs
    have hpu := isPairExpansion_push σu hAs
    rw [rx, har] at hpx
    rw [ru, har] at hpu
    rw [pn_eq _ _ (har ▸ ((isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR)) hpx,
      pn_eq _ _ (har ▸ ((isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR)) hpu,
      pairNum_pushExpansion, pairNum_pushExpansion, cx, cx, cx, cx, cu, cu, cu, cu]
    exact key

  have hX : ∀ b, (rename (Fin.castAdd N) (hsymm (Fin N) ℤ b) :
      MvPolynomial (Fin (N + N)) ℤ).IsHomogeneous b :=
    fun b => (isHomogeneous_hsymm N b).rename_isHomogeneous
  have hU : ∀ b, (rename (Fin.natAdd N) (hsymm (Fin N) ℤ b) :
      MvPolynomial (Fin (N + N)) ℤ).IsHomogeneous b :=
    fun b => (isHomogeneous_hsymm N b).rename_isHomogeneous
  have tele : ∀ (t : Multiset ℕ) (s : ℕ) (S : MvPolynomial (Fin (N + N)) ℤ), S.IsHomogeneous s →
      s + t.sum = m →
      pn (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod) =
        pn (S * (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod) := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intros; rfl
    | cons a t ih =>
      intro s S hS hst
      rw [Multiset.sum_cons] at hst
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have hpX := isHomogeneous_multiset_prod_map _ hX t
      calc pn (S * (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) *
              (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod))
          = pn (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) *
              (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod)) := by
            rw [mul_left_comm]
        _ = pn (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) *
              (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod)) :=
            seg a (s + t.sum) _ (hS.mul hpX) (by omega)
        _ = pn ((S * rename (Fin.natAdd N) (hsymm (Fin N) ℤ a)) *
              (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod) := by
            congr 1
            ring
        _ = pn ((S * rename (Fin.natAdd N) (hsymm (Fin N) ℤ a)) *
              (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod) :=
            ih (s + a) _ (hS.mul (hU a)) (by omega)
        _ = pn (S * (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) *
              (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod)) := by
            rw [mul_assoc]

  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hSym N m G hGm hGsym)
  have hren : ∀ (φ : Fin N → Fin (N + N)), rename φ G =
      ∑ μ, c μ • (μ.parts.map fun b => rename φ (hsymm (Fin N) ℤ b)).prod := by
    intro φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_zsmul, hsymmPart, map_multiset_prod, Multiset.map_map]
    rfl
  have hLHS : pairNum (pointIdeal O y) x x' f g Gs Q = pn (rename (Fin.castAdd N) G) := by
    rw [pn_eq _ _ hGm.rename_isHomogeneous (isPairExpansion_push (Fin.castAdd N) hGs),
      pairNum_pushExpansion]
    simp only [Function.comp_def, Fin.append_left]
  have hRHS : pairNum (pointIdeal O y) u u' f₂ g₂ Hs Q = pn (rename (Fin.natAdd N) G) := by
    rw [pn_eq _ _ hGm.rename_isHomogeneous (isPairExpansion_push (Fin.natAdd N) hHs),
      pairNum_pushExpansion]
    simp only [Function.comp_def, Fin.append_right]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hLHS, hRHS, hren, hren, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  have h := tele μ.parts 0 1 (isHomogeneous_one _ _) (by rw [μ.parts_sum, zero_add])
  simpa only [one_mul] using h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSectionForms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]
  {F : Type*} [Field F] [Algebra F Ω] {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
  {Φ : Type*} [Field Φ] [Algebra Ω Φ]

abbrev projMap (F : Type*) [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    MRing (bundleIdx ι M) F →+* MvPolynomial (Option K) Φ :=
  eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω))) (fun p => C (projCoord y w φ t p) * X p.1)

theorem mem_projIdeal_iff {y : (Σ k, ι k) → Ω} {w : Module.Basis (Fin N) Ω E}
    {φ : Fin M → Module.Dual Ω E} {t : Fin N → Φ} {h : MRing (bundleIdx ι M) F} :
    h ∈ projIdeal F y w φ t ↔ projMap F y w φ t h = 0 :=
  RingHom.mem_ker

def tMon (α : K → ℕ) : MvPolynomial (Option K) Φ := ∏ k, X (some k) ^ α k

theorem tMon_add (α β : K → ℕ) : (tMon (α + β) : MvPolynomial (Option K) Φ) = tMon α * tMon β := by
  simp only [tMon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

def liftN (α : K → ℕ) : Option K → ℕ := fun o => Option.elim o 0 α

theorem liftN_add (α β : K → ℕ) : liftN (α + β) = liftN α + liftN β := by
  funext o; cases o <;> simp [liftN]

def chartMon (F : Type*) [Field F] (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) : MRing (bundleIdx ι M) F :=
  ∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ α k

theorem projMap_X_some (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (k : K) (i : ι k) :
    projMap F y w φ t (X ⟨some k, i⟩) = C (algebraMap Ω Φ (y ⟨k, i⟩)) * X (some k) := by
  simp [projMap, projCoord]

theorem projMap_X_none (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (l : Fin M) :
    projMap F y w φ t (X ⟨none, l⟩) =
      C (∑ i, t i * algebraMap Ω Φ (φ l (w i))) * X none := by
  simp [projMap, projCoord]

theorem sum_truncCoord_one (t : Fin N → Φ) (h0 : 0 < N) (z : Fin N → Φ) :
    ∑ i, truncCoord t 1 i * z i = t ⟨0, h0⟩ * z ⟨0, h0⟩ := by
  rw [Finset.sum_eq_single ⟨0, h0⟩]
  · simp [truncCoord]
  · intro j _ hj
    have : ¬ (j : ℕ) < 1 := by
      intro h; apply hj; ext; simp; omega
    simp [truncCoord, this]
  · simp

theorem projMap_C (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (r : F) :
    projMap F y w φ t (C r) = C (algebraMap Ω Φ (algebraMap F Ω r)) := by
  simp [projMap]

theorem projMap_chartMon (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (α : K → ℕ) :
    projMap F y w φ t (chartMon F M c α) =
      C (algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k)) * tMon α := by
  simp only [chartMon, map_prod, map_pow, projMap_X_some, mul_pow, Finset.prod_mul_distrib, tMon]

theorem isMultiHomog_chartMon (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMon F M c α) (liftN α) := by
  unfold IsMultiHomog chartMon
  have h := IsWeightedHomogeneous.prod (w := blockWeight (bundleIdx ι M)) Finset.univ
    (fun k => (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ α k)
    (fun k => α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (α k))
  convert h using 1
  funext o
  cases o with
  | none => simp [liftN, blockWeight, Finset.sum_apply]
  | some k => simp [liftN, blockWeight, Finset.sum_apply, Pi.single_apply]

theorem isMultiHomog_X_none (l : Fin M) :
    IsMultiHomog (X ⟨none, l⟩ : MRing (bundleIdx ι M) F) (Pi.single none 1) := by
  unfold IsMultiHomog
  exact isWeightedHomogeneous_X F _ _


variable (F M) in
def IsChartForm (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (a : Ω) (n : ℕ)
    (A : MRing (bundleIdx ι M) F) : Prop :=
  IsMultiHomog A (liftN fun _ => n) ∧
    projMap F y w φ t A = C (algebraMap Ω Φ (a * segreVec y c ^ n)) * tMon (fun _ => n)

theorem IsChartForm.pad {y : (Σ k, ι k) → Ω} {w : Module.Basis (Fin N) Ω E}
    {φ : Fin M → Module.Dual Ω E} {t : Fin N → Φ} {c : ∀ k, ι k} {a : Ω} {n : ℕ}
    {A : MRing (bundleIdx ι M) F} (h : IsChartForm (F := F) (M := M) y w φ t c a n A) (m : ℕ) :
    IsChartForm (F := F) (M := M) y w φ t c a (n + m) (A * chartMon F M c (fun _ => m)) := by
  refine ⟨?_, ?_⟩
  · have := h.1.mul (isMultiHomog_chartMon (F := F) (M := M) c (fun _ => m))
    rwa [← liftN_add] at this
  · rw [map_mul, h.2, projMap_chartMon]
    have e : (fun _ : K => n + m) = (fun _ => n) + (fun _ => m) := rfl
    rw [e, tMon_add]
    simp only [segreVec, pow_add, Finset.prod_pow, map_mul]
    ring

theorem exists_chartForm (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {a : Ω} (ha : a ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (A : MRing (bundleIdx ι M) F), IsChartForm (F := F) (M := M) y w φ t c a n A := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, chartMon F M j (fun _ => 1), ?_, ?_⟩
    · exact isMultiHomog_chartMon j _
    · rw [projMap_chartMon, div_mul_eq_mul_div, pow_one, mul_div_assoc, div_self hc, mul_one]
      simp [segreVec]
  | algebraMap r =>
    refine ⟨0, C r, ?_, ?_⟩
    · have e : liftN (fun _ : K => 0) = 0 := by funext o; cases o <;> rfl
      unfold IsMultiHomog
      rw [e]
      exact isWeightedHomogeneous_C _ _
    · rw [projMap_C]
      simp [tMon]
  | add x z _ _ hx hz =>
    obtain ⟨n₁, A₁, h₁⟩ := hx
    obtain ⟨n₂, A₂, h₂⟩ := hz
    have h₁' := h₁.pad n₂
    have h₂' := h₂.pad n₁
    rw [Nat.add_comm n₂ n₁] at h₂'
    refine ⟨n₁ + n₂, _, h₁'.1.add h₂'.1, ?_⟩
    rw [map_add (f := _), h₁'.2, h₂'.2, add_mul, map_add (f := _), C_add, add_mul]
  | mul x z _ _ hx hz =>
    obtain ⟨n₁, A₁, h₁⟩ := hx
    obtain ⟨n₂, A₂, h₂⟩ := hz
    refine ⟨n₁ + n₂, A₁ * A₂, ?_, ?_⟩
    · have := h₁.1.mul h₂.1
      rwa [← liftN_add] at this
    · rw [map_mul, h₁.2, h₂.2]
      have e : (fun _ : K => n₁ + n₂) = (fun _ => n₁) + (fun _ => n₂) := rfl
      rw [e, tMon_add, pow_add]
      simp only [map_mul]
      ring

theorem exists_chartForm_family (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {J : Type*} [Fintype J] (a : J → Ω) (ha : ∀ j, a j ∈ chartRing F (segreVec y) c) :
    ∃ n : ℕ, ∀ m, n ≤ m → ∀ j, ∃ A : MRing (bundleIdx ι M) F,
      IsChartForm (F := F) (M := M) y w φ t c (a j) m A := by
  choose n A hA using fun j => exists_chartForm (M := M) y w φ t c hc (ha j)
  refine ⟨∑ j, n j, fun m hm j => ?_⟩
  have hle : n j ≤ m := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hm
  have := (hA j).pad (m - n j)
  rw [Nat.add_sub_cancel' hle] at this
  exact ⟨_, this⟩

def chartZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℤ) : Ω := ∏ k, y ⟨k, c k⟩ ^ e k

theorem chartZ_add {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e e' : K → ℤ) :
    chartZ y c (e + e') = chartZ y c e * chartZ y c e' := by
  simp only [chartZ, Pi.add_apply, zpow_add₀ (hc _), Finset.prod_mul_distrib]

theorem chartZ_natCast (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (α : K → ℕ) :
    chartZ y c (fun k => (α k : ℤ)) = ∏ k, y ⟨k, c k⟩ ^ α k := by
  simp [chartZ]

theorem segreVec_pow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (n : ℕ) :
    segreVec y c ^ n = chartZ y c (fun _ => (n : ℤ)) := by
  simp [chartZ, segreVec, Finset.prod_pow]

theorem chartZ_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : K → ℤ) :
    chartZ y c e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)

theorem live_of_segreVec_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) :
    ∀ k, y ⟨k, c k⟩ ≠ 0 :=
  fun k => (Finset.prod_ne_zero_iff.mp hc) k (Finset.mem_univ k)

theorem segreVec_ne_zero_of_live {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    segreVec y c ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => hc k

theorem tMon_ne_zero (α : K → ℕ) : (tMon α : MvPolynomial (Option K) Φ) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (X_ne_zero _)

end FlagLineSectionProof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinPointIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar joinCoord mcIdeal mcMap)

namespace JoinPointIdeal

noncomputable section

variable {K : Type} {ι : K → Type}

def joinIdx : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Unit ⊕ (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => .inr ⟨k, i⟩
    | ⟨.inr _, _⟩ => .inl ()
  invFun
    | .inr p => ⟨.inl p.1, p.2⟩
    | .inl _ => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨(k | ⟨⟩), i⟩
    · rfl
    · show (⟨.inr (), (0 : Fin 1)⟩ : Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) = ⟨.inr (), i⟩
      congr 1
      exact (Fin.fin_one_eq_zero i).symm
  right_inv := by
    rintro (⟨⟩ | p) <;> rfl

variable (R : Type) [CommRing R]

def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R ≃+*
    MvPolynomial Unit (MvPolynomial (Σ k, ι k) R) :=
  (renameEquiv R joinIdx).toRingEquiv.trans (sumRingEquiv R Unit (Σ k, ι k))

def tgtEquiv (Ω : Type) [CommRing Ω] : MvPolynomial (K ⊕ Unit) Ω ≃+* MvPolynomial Unit (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.sumComm K Unit)).toRingEquiv.trans (sumRingEquiv Ω Unit K)

variable (Ω : Type) [Field Ω] [Algebra R Ω]

theorem cone_comp (y : (Σ k, ι k) → Ω) :
    ((tgtEquiv (K := K) Ω : MvPolynomial (K ⊕ Unit) Ω →+* MvPolynomial Unit (MvPolynomial K Ω))).comp
        ((mcMap R (joinCoord y (ptCoord (Ω := Ω))) :
            MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →ₐ[R] MvPolynomial (K ⊕ Unit) Ω) :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial (K ⊕ Unit) Ω) =
      (MvPolynomial.map ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* _)).comp
        (srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, MvPolynomial.algebraMap_eq]
  · rintro ⟨(k | ⟨⟩), i⟩
    · simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, joinCoord, joinIdx]
    · simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, joinCoord, joinIdx, ptCoord]

theorem rename_liftVar_eq :
    ((rename (liftVar (ι := ι) ptIdx) : MRing ι R →ₐ[R] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) :
        MRing ι R →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) =
      ((srcEquiv (ι := ι) R).symm : MvPolynomial Unit (MRing ι R) →+* _).comp
        (C : MRing ι R →+* MvPolynomial Unit (MRing ι R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [srcEquiv]
  · intro p
    simp [srcEquiv, liftVar, joinIdx]

end

end JoinPointIdeal

theorem JoinPointIdeal.proof : JoinPointIdeal.Statement := by
  intro R _ Ω _ _ K _ ι _ y
  set φ : MRing ι R →+* MvPolynomial K Ω :=
    ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* MvPolynomial K Ω) with hφ
  have h1 : mcIdeal R (joinCoord y (ptCoord (Ω := Ω))) =
      Ideal.comap (JoinPointIdeal.srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R))
        (RingHom.ker (MvPolynomial.map (σ := Unit) φ)) := by
    ext f
    have hc := RingHom.congr_fun (JoinPointIdeal.cone_comp R Ω y) f
    simp only [RingHom.comp_apply] at hc
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hc]
    simp only [RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]
    exact RingHom.mem_ker
  rw [h1, pointIdeal, show RingHom.ker (pointConeMap R y) = RingHom.ker φ from rfl, ← Ideal.map_coe, JoinPointIdeal.rename_liftVar_eq, ← Ideal.map_map, Ideal.map_coe, Ideal.map_symm, ← MvPolynomial.ker_map]
  rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

