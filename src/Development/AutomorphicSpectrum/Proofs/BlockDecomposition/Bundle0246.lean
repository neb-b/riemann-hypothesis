module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.DlogApprox

theorem alg_core {B : Type} [CommRing B] (J F : Ideal B) (hJF : ∀ a ∈ J, ∀ b ∈ J, a * b ∈ F)
    {H H0 D Y0 I0 W : B} (hH : H ∈ J) (hH0 : H0 ∈ J) (hD : D ∈ J) (hI : Y0 * I0 = 1)
    (hW : W * ((1 + H0) * Y0) = 1) :
    (1 + H) * (Y0 + D) * W - 1 - (D * I0 + H - H0) ∈ F := by
  set C := W * Y0 with hCdef
  have hC : C * (1 + H0) = 1 := by rw [hCdef]; linear_combination hW
  have hWC : W = C * I0 := by rw [hCdef]; linear_combination (-W) * hI
  set A := H + D * I0 + H * (D * I0) with hA
  have hAJ : A ∈ J := J.add_mem (J.add_mem hH (J.mul_mem_right _ hD)) (J.mul_mem_left _ (J.mul_mem_right _ hD))
  have e : (1 + H) * (Y0 + D) * W - 1 - (D * I0 + H - H0) =
      (C * H0) * H0 - (A * C) * H0 + H * (D * I0) := by
    rw [hWC, hA]
    linear_combination (1 + H) * C * hI + (1 - H0 + (H + D * I0 + H * (D * I0))) * hC
  rw [e]
  exact F.add_mem (F.sub_mem (hJF _ (J.mul_mem_left _ hH0) _ hH0) (hJF _ (J.mul_mem_right _ hAJ) _ hH0))
    (hJF _ hH _ (J.mul_mem_right _ hD))

theorem plogK_sub_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (F : Ideal B) {s : ℕ} (hs : 1 ≤ s)
    {x : B} (hx : x ∈ J) (h : ∀ k, 2 ≤ k → δ.dpow k x ∈ F) : plogK δ s x - x ∈ F := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  unfold plogK
  rw [Finset.sum_range_succ']
  have e : (-1 : B) ^ 0 * ((Nat.factorial 0 : ℕ) : B) * δ.dpow (0 + 1) x = x := by
    simp [δ.dpow_one hx]
  rw [e, add_sub_cancel_right]
  exact F.sum_mem fun k _ => F.mul_mem_left _ (h _ (by omega))

section Fr
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem form_one {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (i : Fin d) (x : Φ.A.obj E.D)
    (u : ComposableArrows C 1) :
    E.form σ ![i] x u = E.a σ i (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form
  rw [Fin.prod_univ_one]
  congr 1
  have e : ∀ (h : (Fin.succ (0 : Fin 1)) ⟶ Fin.last 1) (z : Φ.A.obj (u.obj (Fin.last 1))),
      (Φ.A.map (u.map h)).hom z = z := by
    intro h z
    have : h = 𝟙 (Fin.last 1) := Subsingleton.elim _ _
    have e2 : u.map h = 𝟙 (u.obj (Fin.last 1)) := (congrArg u.map this).trans (u.map_id _)
    have e3 : Φ.A.map (u.map h) = 𝟙 (Φ.A.obj (u.obj (Fin.last 1))) := (congrArg Φ.A.map e2).trans (Φ.A.map_id _)
    rw [e3]
    rfl
  exact e _ _

theorem mul2 {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (T : C) : ∀ a ∈ Φ.J.S T, ∀ b ∈ Φ.J.S T, a * b ∈ (Fil 2).S T := by
  intro a ha b hb
  have h1 : ∀ z ∈ Φ.J.S T, z ∈ (Fil ((1 : ℕ) : ℤ)).S T := fun z hz => by
    rw [Nat.cast_one, hF.one]; exact hz
  exact hF.mul 1 1 T (h1 a ha) (h1 b hb)

theorem const1 {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} {E : Frame Φ d} (hc : E.GrConst Fil) {T : C}
    (a b : E.D ⟶ T) (x : Φ.A.obj E.D) : (Φ.A.map a).hom x - (Φ.A.map b).hom x ∈ Φ.J.S T := by
  have h := hc 0 a b (x := x) (by rw [Nat.cast_zero, hF.top 0 le_rfl E.D]; trivial)
  rw [Nat.cast_zero, zero_add, hF.one] at h
  exact h

theorem frame_core {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (ht : Taylor Fil E p) (σ : ∀ T : C, E.D ⟶ T)
    (G : Φ.A.obj E.D) (hG : IsUnit G) {T T' : C} (φ : T ⟶ T') {H H0 W : Φ.A.obj T'}
    (hH : H ∈ Φ.J.S T') (hH0 : H0 ∈ Φ.J.S T')
    (hW : W * ((1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G) = 1) :
    (1 + H) * (Φ.A.map (σ T')).hom G * W - 1 -
      (∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) + (H - H0)) ∈ (Fil 2).S T' := by
  set v := (Φ.A.map (σ T ≫ φ)).hom with hv
  set w := (Φ.A.map (σ T')).hom with hw
  have hI : v G * v (Ring.inverse G) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hG, map_one]
  have hD : w G - v G ∈ Φ.J.S T' := const1 hF hc _ _ G
  have h1 := alg_core (Φ.J.S T') ((Fil 2).S T') (mul2 hF T') hH hH0 hD hI hW
  have h2 := ((Fil 2).S T').mul_mem_left (v (Ring.inverse G)) (ht T' (σ T') (σ T ≫ φ) G)
  have h3 : ∑ i, E.a σ i φ * (v (Ring.inverse G * p i G) - w (Ring.inverse G * p i G)) ∈ (Fil 2).S T' :=
    ((Fil 2).S T').sum_mem fun i _ => mul2 hF T' _ (E.mem i _ _) _ (const1 hF hc _ _ _)
  have h4 : ∑ i, E.a σ i φ * (v (Ring.inverse G * p i G) - w (Ring.inverse G * p i G)) =
      v (Ring.inverse G) * ∑ i, E.a σ i φ * v (p i G) - ∑ i, E.a σ i φ * w (Ring.inverse G * p i G) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul v]
    ring
  have h5 : (∑ k, E.τ k (σ T ≫ φ) (σ T') * v (p k G)) = ∑ i, E.a σ i φ * v (p i G) := rfl
  rw [h4] at h3
  change v (Ring.inverse G) * (w G - v G - ∑ k, E.τ k (σ T ≫ φ) (σ T') * v (p k G)) ∈ _ at h2
  rw [h5] at h2
  have e : (1 + H) * w G * W - 1 - (∑ i, E.a σ i φ * w (Ring.inverse G * p i G) + (H - H0)) =
      ((1 + H) * (v G + (w G - v G)) * W - 1 - ((w G - v G) * v (Ring.inverse G) + H - H0)) +
      v (Ring.inverse G) * (w G - v G - ∑ i, E.a σ i φ * v (p i G)) +
      (v (Ring.inverse G) * (∑ i, E.a σ i φ * v (p i G)) - ∑ i, E.a σ i φ * w (Ring.inverse G * p i G)) := by
    ring
  rw [e]
  exact ((Fil 2).S T').add_mem (((Fil 2).S T').add_mem h1 h2) h3

end Fr

section Fr2
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem frame_main {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (ht : Taylor Fil E p) (σ : ∀ T : C, E.D ⟶ T)
    (G : Φ.A.obj E.D) (hG : IsUnit G) (gh : ∀ T, Φ.A.obj T)
    (hg : ∀ T, gh T - (Φ.A.map (σ T)).hom G ∈ Φ.J.S T)
    (hun : ∀ T, ∀ x ∈ Φ.J.S T, IsUnit (1 + x)) :
    (∀ T, gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 ∈ Φ.J.S T) ∧
    ∀ {T T' : C} (φ : T ⟶ T'),
      (gh T' * Ring.inverse ((Φ.A.map φ).hom (gh T)) - 1 ∈ Φ.J.S T') ∧
      gh T' * Ring.inverse ((Φ.A.map φ).hom (gh T)) - 1 -
        (∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) +
          ((gh T' * Ring.inverse ((Φ.A.map (σ T')).hom G) - 1) -
            (Φ.A.map φ).hom (gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1))) ∈ (Fil 2).S T' := by
  have hy : ∀ T, IsUnit ((Φ.A.map (σ T)).hom G) := fun T => hG.map (Φ.A.map (σ T)).hom
  have hyi : ∀ T, (Φ.A.map (σ T)).hom G * Ring.inverse ((Φ.A.map (σ T)).hom G) = 1 :=
    fun T => Ring.mul_inverse_cancel _ (hy T)
  have hh : ∀ T, gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 ∈ Φ.J.S T := by
    intro T
    have e : gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 =
        (gh T - (Φ.A.map (σ T)).hom G) * Ring.inverse ((Φ.A.map (σ T)).hom G) := by
      linear_combination hyi T
    rw [e]
    exact (Φ.J.S T).mul_mem_right _ (hg T)
  refine ⟨hh, ?_⟩
  intro T T' φ
  set H := gh T' * Ring.inverse ((Φ.A.map (σ T')).hom G) - 1 with hHd
  set h0 := gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 with hh0
  set H0 := (Φ.A.map φ).hom h0 with hH0d
  have hHm : H ∈ Φ.J.S T' := hh T'
  have hH0m : H0 ∈ Φ.J.S T' := Φ.J.map_mem φ (hh T)
  have e1 : gh T = (1 + h0) * (Φ.A.map (σ T)).hom G := by
    rw [hh0]; linear_combination (-gh T) * hyi T
  have e2 : gh T' = (1 + H) * (Φ.A.map (σ T')).hom G := by
    rw [hHd]; linear_combination (-gh T') * hyi T'
  have hU : IsUnit (gh T) := by
    rw [e1]; exact (hun T _ (hh T)).mul (hy T)
  have e3 : (Φ.A.map φ).hom (gh T) = (1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G := by
    rw [e1, map_mul, map_add (f := _), map_one, Φ.A.map_comp]
    rfl
  have hW : Ring.inverse ((Φ.A.map φ).hom (gh T)) * ((1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G) = 1 := by
    rw [← e3]
    exact Ring.inverse_mul_cancel _ (hU.map (Φ.A.map φ).hom)
  have key := frame_core hF E hc p ht σ G hG φ hHm hH0m hW
  rw [← e2] at key
  refine ⟨?_, key⟩
  have hle : (Fil 2).S T' ≤ Φ.J.S T' := by
    rw [← hF.one]; exact hF.anti (by norm_num) T'
  have hs : ∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) + (H - H0) ∈ Φ.J.S T' :=
    (Φ.J.S T').add_mem ((Φ.J.S T').sum_mem fun i _ => (Φ.J.S T').mul_mem_right
      ((Φ.A.map (σ T')).hom (Ring.inverse G * p i G)) (E.mem i (σ T ≫ φ) (σ T'))) ((Φ.J.S T').sub_mem hHm hH0m)
  have h6 := (Φ.J.S T').add_mem (hle key) hs
  rw [sub_add_cancel] at h6
  exact h6

end Fr2

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ), 2 ≤ s → ∀ {V V' : X.Opens} (hVV : V ≤ V') {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s t E ε →
    ∀ (p : Fin d → (sP (KS q s {V})).A.obj E.D → (sP (KS q s {V})).A.obj E.D), Taylor (sFil (KS q s {V})) E p →
    ∀ (σ : ∀ T, E.D ⟶ T) (g : Γ(X, V')), IsUnit g → ∀ (ĝ : ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B),
      (∀ T, Ideal.Quotient.mk T.obj.J (ĝ T) = ev T.obj (ks_in q s V' _ T.property) g) →
      ∃ h : ∀ T, (sP (KS q s {V})).A.obj T, (∀ T, h T ∈ (sP (KS q s {V})).J.S T) ∧ ∀ u : ComposableArrows (KS q s {V}).FullSubcategory 1,
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s ĝ) u) -
          (∑ i, E.form σ ![i] (Ring.inverse (ε (rs hVV g)) * p i (ε (rs hVV g))) u +
            (h (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h (u.obj 0)))) ∈
          (sFil (KS q s {V}) 2).S _ := by
  intro K _ _ X q s hs V V' hVV d t E ε hL p ht σ g hg ĝ hĝ
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  obtain ⟨hc, -, -, h4, -⟩ := hL
  have hG : IsUnit (ε (rs hVV g)) := (hg.map (rs hVV)).map ε
  let gh : ∀ T : (KS q s {V}).FullSubcategory, (sP (KS q s {V})).A.obj T :=
    fun T => ĝ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T)
  have hgl : ∀ T, gh T - ((sP (KS q s {V})).A.map (σ T)).hom (ε (rs hVV g)) ∈ (sP (KS q s {V})).J.S T := by
    intro T
    have a1 := hĝ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T)
    have a2 := h4 T (σ T) (rs hVV g)
    have a3 := GlobalTheory.CompanionTheory.GrForm.ev_res hVV T.obj (ks_in q s V' _ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T).property)
      (ks_in q s V _ T.property) g
    exact Ideal.Quotient.eq.1 (a1.trans (a3.symm.trans a2))
  have hun : ∀ T, ∀ x ∈ (sP (KS q s {V})).J.S T, IsUnit (1 + x) := by
    intro T x hx
    have hn : IsNilpotent (show T.obj.B from x) := by
      obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.ConeZcls.J_nil T.obj
      refine ⟨n, ?_⟩
      have h1 : (show T.obj.B from x) ^ n ∈ T.obj.J ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at h1
      simpa using h1
    exact hn.isUnit_one_add
  obtain ⟨m1, m2⟩ := frame_main hF E hc p ht σ (ε (rs hVV g)) hG gh hgl hun
  refine ⟨fun T => gh T * Ring.inverse (((sP (KS q s {V})).A.map (σ T)).hom (ε (rs hVV g))) - 1, m1, fun u => ?_⟩
  obtain ⟨b1, b2⟩ := m2 (u.map (homOfLE (Fin.zero_le (Fin.last 1))))
  have b3 := plogK_sub_mem (u.obj (Fin.last 1)).obj.δ
    (show Ideal (u.obj (Fin.last 1)).obj.B from (sFil (KS q s {V}) 2).S (u.obj (Fin.last 1)))
    (s := s) (by omega) b1 (fun k hk => hF.anti (by exact_mod_cast hk) _ (hF.dp_mem k _ b1))
  have b4 := ((sFil (KS q s {V}) 2).S (u.obj (Fin.last 1))).add_mem b3 b2
  rw [sub_add_sub_cancel] at b4
  simp only [form_one]
  exact b4

end GlobalTheory.CompanionTheory.ConeLocal.DlogApprox
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateEventuallyZero
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Nonv

theorem ltIter_succ_eq {B : Type} [CommRing B] (ϖ : B) (q n : ℕ) (x : B) :
    ltIter ϖ q (n + 1) x = ϖ * ltIter ϖ q n x + ltIter ϖ q n x ^ q := by
  simp only [ltIter, Function.iterate_succ_apply']

theorem norm_step_eq {C : Type} [NormedField C] [IsUltrametricDist C] (a c : C) (q : ℕ) (hq : 2 ≤ q)
    (h : ‖c‖ ^ (q - 1) < ‖a‖) : ‖a * c + c ^ q‖ = ‖a‖ * ‖c‖ := by
  by_cases hc : c = 0
  · subst hc
    have : q ≠ 0 := by omega
    simp [this]
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hlt : ‖c ^ q‖ < ‖a * c‖ := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      rw [norm_pow, norm_mul, pow_succ]
      simp only [Nat.add_sub_cancel] at h
      exact mul_lt_mul_of_pos_right h hcpos
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt), max_eq_left hlt.le, norm_mul]

theorem norm_step_le {C : Type} [NormedField C] [IsUltrametricDist C] (a c : C) (q : ℕ) (hq : 2 ≤ q) :
    ‖a * c + c ^ q‖ ≤ max ‖a‖ (‖c‖ ^ (q - 1)) * ‖c‖ := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [norm_mul, norm_pow, pow_succ, max_mul_of_nonneg _ _ (norm_nonneg c)]

theorem exists_norm_geometric {C : Type} [NormedField C] [IsUltrametricDist C] (a : C) (q : ℕ) (hq : 2 ≤ q)
    (ha0 : a ≠ 0) (ha : ‖a‖ < 1) (c : ℕ → C) (hc : ∀ n, c (n + 1) = a * c n + c n ^ q)
    (h0 : ‖c 0‖ < 1) : ∃ n, ∀ j, ‖c (n + j)‖ = ‖a‖ ^ j * ‖c n‖ := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set ρ := max ‖a‖ (‖c 0‖ ^ (q - 1)) with hρ
  have hρ1 : ρ < 1 := max_lt ha (pow_lt_one₀ (norm_nonneg _) h0 (by omega))
  have hρ0 : 0 ≤ ρ := hapos.le.trans (le_max_left _ _)
  have hdec : ∀ n, ‖c n‖ ≤ ρ ^ n * ‖c 0‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hle : ‖c n‖ ≤ ‖c 0‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hρ0 hρ1.le))
      have hm : max ‖a‖ (‖c n‖ ^ (q - 1)) ≤ ρ :=
        max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hle _)
      rw [hc n]
      calc ‖a * c n + c n ^ q‖ ≤ max ‖a‖ (‖c n‖ ^ (q - 1)) * ‖c n‖ := norm_step_le a _ q hq
        _ ≤ ρ * (ρ ^ n * ‖c 0‖) := mul_le_mul hm ih (norm_nonneg _) hρ0
        _ = ρ ^ (n + 1) * ‖c 0‖ := by ring
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hapos hρ1
  have hcn : ‖c n‖ < ‖a‖ :=
    ((hdec n).trans (mul_le_of_le_one_right (pow_nonneg hρ0 n) h0.le)).trans_lt hn
  have hsmall : ∀ x : C, ‖x‖ ≤ ‖c n‖ → ‖x‖ ^ (q - 1) < ‖a‖ := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := hx.trans (hcn.trans ha).le
    exact ((pow_le_of_le_one (norm_nonneg _) hx1 (by omega)).trans hx).trans_lt hcn
  refine ⟨n, fun j => ?_⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have hle : ‖c (n + j)‖ ≤ ‖c n‖ := by
      rw [ih]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hapos.le ha.le)
    rw [← add_assoc, hc (n + j), norm_step_eq a _ q hq (hsmall _ hle), ih]
    ring

variable {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}

theorem ltIter_mem (hE : PerEnv S F ϖ) (q : ℕ) {Q : B} (hQ : Q ∈ S) (n : ℕ) : ltIter ϖ q n Q ∈ S := by
  induction n with
  | zero => simpa [ltIter] using hQ
  | succ n ih =>
    rw [ltIter_succ_eq]
    exact S.add_mem (S.mul_mem hE.mem ih) (S.pow_mem ih q)

theorem ltIter_mem_succ (hE : PerEnv S F ϖ) (ϖ' : B) (hϖ : ϖ * ϖ' = 1) (q : ℕ) (hq : 2 ≤ q) {Q : B} (hQ : Q ∈ S)
    (hT : Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0) (n m : ℕ) (hm : 1 ≤ m)
    (hy : ltIter ϖ q n Q ∈ F m) : ltIter ϖ q n Q ∈ F (m + 1) := by
  have hanti : Antitone F := antitone_nat_of_succ_le hE.anti
  have hD : ∀ j, ltIter ϖ q (n + j) Q - ϖ ^ j * ltIter ϖ q n Q ∈ F (m + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hym : ltIter ϖ q (n + j) Q ∈ F m := by
        have h1 := (F m).add_mem (hE.anti m ih) ((F m).mul_mem_left (ϖ ^ j) hy)
        simpa using h1
      have hsq : ltIter ϖ q (n + j) Q * ltIter ϖ q (n + j) Q ∈ F (m + 1) :=
        hanti (by omega : m + 1 ≤ m + m) (hE.mul_le m m (Ideal.mul_mem_mul hym hym))
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
      have he : ltIter ϖ (r + 2) (n + (j + 1)) Q - ϖ ^ (j + 1) * ltIter ϖ (r + 2) n Q =
          ϖ * (ltIter ϖ (r + 2) (n + j) Q - ϖ ^ j * ltIter ϖ (r + 2) n Q) +
            ltIter ϖ (r + 2) (n + j) Q ^ r * (ltIter ϖ (r + 2) (n + j) Q * ltIter ϖ (r + 2) (n + j) Q) := by
        rw [← add_assoc, ltIter_succ_eq]
        ring
      rw [he]
      exact (F (m + 1)).add_mem ((F (m + 1)).mul_mem_left _ ih) ((F (m + 1)).mul_mem_left _ hsq)
  obtain ⟨c, hc⟩ := hT (m + 1)
  refine hE.closed (m + 1) _ (ltIter_mem hE q hQ n) fun M => ?_
  obtain ⟨N, hN⟩ := hc (M + c)
  obtain ⟨s, hs, hd⟩ := hN (n + N) (by omega)
  refine ⟨ϖ ^ n * s, S.mul_mem (S.pow_mem hE.mem n) hs, ?_⟩
  have h1 : ϖ ^ c * ϖ' ^ c = 1 := by rw [← mul_pow, hϖ, one_pow]
  have h2 : ϖ ^ n * ϖ' ^ n = 1 := by rw [← mul_pow, hϖ, one_pow]
  have h3 : ϖ ^ N * ϖ' ^ N = 1 := by rw [← mul_pow, hϖ, one_pow]
  have he : ltIter ϖ q n Q - ϖ ^ M * (ϖ ^ n * s) =
      ϖ ^ n * ϖ' ^ c * (ϖ ^ c * (ϖ' ^ (n + N) * ltIter ϖ q (n + N) Q - 0) - ϖ ^ (M + c) * s) -
        ϖ' ^ N * (ltIter ϖ q (n + N) Q - ϖ ^ N * ltIter ϖ q n Q) := by
    linear_combination (-ltIter ϖ q n Q) * h3 +
      (ϖ ^ M * ϖ ^ n * s - ϖ' ^ N * ltIter ϖ q (n + N) Q * (ϖ ^ n * ϖ' ^ n)) * h1 -
      ϖ' ^ N * ltIter ϖ q (n + N) Q * h2
  rw [he]
  exact (F (m + 1)).sub_mem ((F (m + 1)).mul_mem_left _ hd) ((F (m + 1)).mul_mem_left _ (hD N))

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem exists_ltIter_mem_one (ϖ' : B) (hϖ : ϖ * ϖ' = 1) (θ : B →+* C) (hθ : ∀ x, θ x = 0 ↔ x ∈ F 1)
    (hS : ∀ s ∈ S, ‖θ s‖ ≤ 1) (ha : ‖θ ϖ‖ < 1) (q : ℕ) (hq : 2 ≤ q) (Q : B) (hQ : Q ∈ S)
    (hQM : ∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M))
    (hT : Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0) : ∃ n, ltIter ϖ q n Q ∈ F 1 := by
  have haa : θ ϖ * θ ϖ' = 1 := by rw [← map_mul, hϖ, map_one]
  have ha0 : θ ϖ ≠ 0 := left_ne_zero_of_mul_eq_one haa
  have hapos : 0 < ‖θ ϖ‖ := norm_pos_iff.mpr ha0
  have hnn : ‖θ ϖ‖ * ‖θ ϖ'‖ = 1 := by rw [← norm_mul, haa, norm_one]
  have hpos' : 0 < ‖θ ϖ'‖ := by
    have := right_ne_zero_of_mul_eq_one haa
    exact norm_pos_iff.mpr this
  have h0 : ‖θ (ltIter ϖ q 0 Q)‖ < 1 := by
    obtain ⟨M, hM, s, hs, hd⟩ := hQM
    have e : θ Q ^ M = θ ϖ * θ s := by
      have := (hθ _).mpr hd
      simp only [map_sub, map_mul, map_pow, pow_one] at this
      exact sub_eq_zero.mp this
    by_contra hcon
    have h1 : (1 : ℝ) ≤ ‖θ Q‖ := by simpa [ltIter] using hcon
    have h2 : (1 : ℝ) ≤ ‖θ Q‖ ^ M := one_le_pow₀ h1
    have h3 : ‖θ Q‖ ^ M = ‖θ ϖ‖ * ‖θ s‖ := by rw [← norm_pow, e, norm_mul]
    have h4 : ‖θ ϖ‖ * ‖θ s‖ < 1 :=
      (mul_le_of_le_one_right hapos.le (hS s hs)).trans_lt ha
    linarith
  obtain ⟨n, hn⟩ := exists_norm_geometric (θ ϖ) q hq ha0 ha (fun n => θ (ltIter ϖ q n Q))
    (fun n => by simp only [ltIter_succ_eq, map_add (f := _), map_mul, map_pow]) h0
  refine ⟨n, (hθ _).mp ?_⟩
  by_contra hne
  have hcpos : 0 < ‖θ (ltIter ϖ q n Q)‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := hT 1
  have hK : 0 < ‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖ := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hK ha
  obtain ⟨N, hN⟩ := hc m
  obtain ⟨s, hs, hd⟩ := hN (n + N) (by omega)
  have e := (hθ _).mpr hd
  simp only [map_sub, map_mul, map_pow, map_zero, sub_zero] at e
  have e2 : ‖θ ϖ‖ ^ c * (‖θ ϖ'‖ ^ (n + N) * ‖θ (ltIter ϖ q (n + N) Q)‖) = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
    have := congrArg norm (sub_eq_zero.mp e)
    simpa only [norm_mul, norm_pow] using this
  have hNN : ‖θ ϖ‖ ^ N * ‖θ ϖ'‖ ^ N = 1 := by rw [← mul_pow, hnn, one_pow]
  have e3 : ‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖ = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
    rw [← e2, hn N, pow_add]
    linear_combination (-(‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖)) * hNN
  have h5 : ‖θ ϖ‖ ^ m * ‖θ s‖ ≤ ‖θ ϖ‖ ^ m :=
    mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hs)
  linarith

end GlobalTheory.CompanionTheory.LTPer.Nonv

namespace GlobalTheory.CompanionTheory.LTPer


open GlobalTheory.CompanionTheory.LTPer.Nonv in
theorem exists_ltIter_eq_zero_of_tends : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0 → ∃ n, ltIter ϖ q n Q = 0 := by
  intro B _ S F ϖ C _ _ hE ϖ' hϖ θ hθ hS ha q hq Q hQ hQM hT
  obtain ⟨n, hn⟩ := exists_ltIter_mem_one ϖ' hϖ θ hθ hS ha q hq Q hQ hQM hT
  refine ⟨n, hE.sep _ fun k => ?_⟩
  have hall : ∀ m, 1 ≤ m → ltIter ϖ q n Q ∈ F m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hn
    | succ m hm ih => exact ltIter_mem_succ hE ϖ' hϖ q hq hQ hT n m hm ih
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hE.top]; exact Submodule.mem_top
  · exact hall k hk

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateLimitKernelZero
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem theta_period_eq_zero_of_theta_eq_zero :
    ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q, θ Q = 0 → ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → θ t = 0 := by
  intro B _ S F ϖ C _ _ ϖ' hϖ θ hker hS hlt q hq Q hQ t ht
  have hy : ∀ n, θ (ltIter ϖ q n Q) = 0 := by
    intro n
    induction n with
    | zero => simpa [ltIter] using hQ
    | succ n ih =>
      have hs : ltIter ϖ q (n + 1) Q = ϖ * ltIter ϖ q n Q + (ltIter ϖ q n Q) ^ q := by
        simp only [ltIter, Function.iterate_succ_apply']
      rw [hs, map_add (f := _), map_mul, map_pow, ih]
      simp [show q ≠ 0 by omega]
  have hne : θ ϖ ≠ 0 := by
    intro h0
    have h1 : θ ϖ * θ ϖ' = 1 := by rw [← map_mul, hϖ, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hapos : 0 < ‖θ ϖ‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := ht 1
  have hbound : ∀ m : ℕ, ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ ‖θ ϖ‖ ^ m := by
    intro m
    obtain ⟨N, hN⟩ := hc m
    obtain ⟨s, hsS, hs⟩ := hN N le_rfl
    have h0 := (hker _).mpr hs
    simp only [map_sub, map_mul, map_pow, hy, mul_zero, zero_sub] at h0
    have h1 : θ ϖ ^ c * θ t = -(θ ϖ ^ m * θ s) := by linear_combination -h0
    have h2 : ‖θ ϖ‖ ^ c * ‖θ t‖ = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
      have := congrArg norm h1
      simpa [norm_mul, norm_pow, norm_neg] using this
    rw [h2]
    exact mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hsS)
  have hlim : Filter.Tendsto (fun m : ℕ => ‖θ ϖ‖ ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hapos.le hlt
  have hle : ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ 0 := ge_of_tendsto' hlim hbound
  have hz : ‖θ t‖ ≤ 0 := by
    by_contra hcon
    have : 0 < ‖θ ϖ‖ ^ c * ‖θ t‖ := mul_pos (pow_pos hapos c) (not_le.mp hcon)
    linarith
  exact norm_le_zero_iff.mp hz

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcCup
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupTrans

theorem omMor_cup {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ)
    {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {c' : Λ →+* b'.R} (h : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    {p q s : ℕ} (e : p + q = s) (x : CH.H (OM L c) p) (y : CH.H (OM L c) q) :
    (omMor m (RingHom.id Λ) h).pull s ((CH.mulP (OA L c)).cup e x y) =
      (CH.mulP (OA L' c')).cup e ((omMor m (RingHom.id Λ) h).pull p x) ((omMor m (RingHom.id Λ) h).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (CH.mulP (OA L c)) (CH.mulP (OA L' c')) m.functor (omMor m (RingHom.id Λ) h).τ
    (omMor m (RingHom.id Λ) h).τ (omMor m (RingHom.id Λ) h).τ (omMor m (RingHom.id Λ) h).nat
    (omMor m (RingHom.id Λ) h).nat (omMor m (RingHom.id Λ) h).nat (fun _ _ _ => rfl) e x y

theorem redHc_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) {i j s : ℕ} (e : i + j = s) (x : Hc F κ k m i) (y : Hc F κ k m j), redHc F κ k h s ((CH.mulP (OcA F κ k m)).cup e x y) = (CH.mulP (OcA F κ k n)).cup e (redHc F κ k h i x) (redHc F κ k h j y) := by
  intro l _ O _ F κ k m n h i j s e x y
  exact omMor_cup _ _ e x y

end GlobalTheory.CompanionTheory.CupTrans
end

