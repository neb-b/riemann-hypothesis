module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsHolomorphicGeneratorReadingAutomorphy
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValGenRd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt

attribute [local instance] Over.cartesianMonoidalCategory

theorem differentiableAt_prod {E K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset K)
    (f : K → E → ℂ) (z : E) (h : ∀ k, DifferentiableAt ℂ (f k) z) :
    DifferentiableAt ℂ (fun w => ∏ k ∈ s, f k w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

private theorem preimage_eq_univ_iff_forall_mem {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ ∀ p, x p ∈ U := by
  constructor
  · intro h p
    exact h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  · intro h p _
    exact h p

section LC

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

theorem top_le_wchart_iff (φ : K → (Y ⟶ X)) (j : K → L.ι) (x : Sp ℂ ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  simp only [preimage_eq_univ_iff_forall_mem]
  unfold LB.wchart
  constructor
  · intro h k p
    exact Set.mem_iInter.1 (h p) k
  · intro h p
    exact Set.mem_iInter.2 fun k => h k p

theorem top_le_inf {x : Sp ℂ ⟶ Y} {U V : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := by
  rw [preimage_eq_univ_iff_forall_mem] at h h' ⊢
  intro p
  exact TopologicalSpace.Opens.mem_inf.2 ⟨h p, h' p⟩

theorem val_prod (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : K → Γ(Y, U)ˣ) :
    valAt' x U (∏ k, u k).val = ∏ k, valAt' x U (u k).val := by
  rw [Units.coe_prod]
  exact map_prod (valHom x U h) _ _

private theorem valAt'_app_hom_eq_valAt'_comp {W V : Scheme.{0}} (x : Sp ℂ ⟶ V) (ψ : V ⟶ W) (U : W.Opens) (f : Γ(W, U)) :
    valAt' x (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) = valAt' (x ≫ ψ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U := h
    rw [dite_eq_left h, dite_eq_left h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U := h
    rw [dite_eq_right h, dite_eq_right h']

private theorem valAt'_pullU_eq_valAt'_comp {W V : Scheme.{0}} (x : Sp ℂ ⟶ V) (ψ : V ⟶ W) (U : W.Opens) (u : Γ(W, U)ˣ) :
    valAt' x (ψ ⁻¹ᵁ U) (pullU ψ U u).val = valAt' (x ≫ ψ) U u.val := by
  unfold pullU
  rw [Units.coe_map]
  exact valAt'_app_hom_eq_valAt'_comp x ψ U u.val

private theorem valAt'_res_unit_eq {W : Scheme.{0}} (x : Sp ℂ ⟶ W) {U V : W.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (u : Γ(W, U)ˣ) : valAt' x V (res hVU u).val = valAt' x U u.val := by
  unfold res
  rw [Units.coe_map]
  exact valAt'_res x hVU h u.val

private theorem valAt'_unit_zpow' {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(W, U)ˣ)
    (n : ℤ) : valAt' x U (u ^ n).val = valAt' x U u.val ^ n := by
  have e := congrArg Units.val (map_zpow (Units.map (valHom x U h).toMonoidHom) u n)
  rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map] at e
  exact e

theorem val_linComb_g (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  unfold LB.LinComb
  dsimp only
  rw [val_prod p _ h]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [valAt'_unit_zpow' p _ h]
  congr 1
  exact (valAt'_res_unit_eq p _ h _).trans (valAt'_pullU_eq_valAt'_comp p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))

theorem val_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Sp ℂ ⟶ Y) (j j' : K → L.ι) (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p (LB.wchart L φ j) (t.s j).val =
      (∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' p (LB.wchart L φ j') (t.s j').val := by
  have e := congrArg (fun u => valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) (ht j j')
  simp only [Units.val_mul] at e
  have e1 := valAt'_res_unit_eq p (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) h (t.s j)
  have e2 := valAt'_res_unit_eq p (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') h (t.s j')
  have e3 := val_linComb_g L φ ε p j j' h
  exact e1.symm.trans (e.trans ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) e3 e2)))

theorem exists_chart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (x : Sp ℂ ⟶ Y) :
    ∃ j : K → L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j := by
  have hp : ∀ k, ∃ i, (x ≫ φ k) (default : PrimeSpectrum ℂ) ∈ L.U i := fun k => by
    have h0 : (x ≫ φ k) (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 h0
  choose j hj using hp
  refine ⟨j, (top_le_wchart_iff L φ j x).2 fun k => (preimage_eq_univ_iff_forall_mem _ _).2 fun p => ?_⟩
  rw [Subsingleton.elim (α := PrimeSpectrum ℂ) p default]
  exact hj k

end LC

section Rd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε))

theorem top_le_chart {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left) {j : K → L.L.ι}
    (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) (k : K) : ⊤ ≤ (Φ.e (p k)).left ⁻¹ᵁ L.L.U (j k) := by
  have h := (top_le_wchart_iff L.L φ j q).1 hj k
  rwa [hq k] at h

theorem prod_fr_ne {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left) {j : K → L.L.ι}
    (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) : ∏ k, Φ.fr (j k) (p k) ^ ε k ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_
  exact Φ.fr_ne _ _ (top_le_chart Φ φ hq hj k)

theorem genRd_of_chart (ht : t.IsGen) {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left)
    {j' : K → L.L.ι} (hj' : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j') :
    Φ.GenRd φ ε t q p (valAt' q (LB.wchart L.L φ j') (t.s j').val / ∏ k, Φ.fr (j' k) (p k) ^ ε k) := by
  refine ⟨hq, fun j hj => ?_⟩
  have hg : ∀ k, valAt' (q ≫ φ k) (L.L.U (j k) ⊓ L.L.U (j' k)) (L.L.g (j k) (j' k)).val =
      Φ.fr (j k) (p k) / Φ.fr (j' k) (p k) := fun k => by
    rw [hq k, eq_div_iff (Φ.fr_ne _ _ (top_le_chart Φ φ hq hj' k))]
    exact (Φ.fr_g _ _ _ (top_le_inf (top_le_chart Φ φ hq hj k) (top_le_chart Φ φ hq hj' k))).symm
  have hA := prod_fr_ne Φ φ ε hq hj
  have hB := prod_fr_ne Φ φ ε hq hj'
  rw [val_isGen L.L φ ε t ht q j j' (top_le_inf hj hj')]
  simp only [hg, div_zpow, Finset.prod_div_distrib]
  field_simp

theorem genRd_eq {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} {u : ℂ} (hu : Φ.GenRd φ ε t q p u)
    {j : K → L.L.ι} (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) :
    u = valAt' q (LB.wchart L.L φ j) (t.s j).val / ∏ k, Φ.fr (j k) (p k) ^ ε k := by
  rw [eq_div_iff (prod_fr_ne Φ φ ε hu.1 hj)]
  exact (hu.2 j hj).symm

private theorem valAt'_unit_val_ne_zero {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (u : Γ(W, U)ˣ) : valAt' x U u.val ≠ 0 :=
  (u.isUnit.map (valHom x U h)).ne_zero

end Rd

theorem exists_reading : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (p : K → (Fin N → ℂ) → Fin g → ℂ), IsHolFam q → (∀ k, Differentiable ℂ (p k)) → (∀ z k, q z ≫ φ k = (Φ.e (p k z)).left) → ∃ v : (Fin N → ℂ) → ℂ, Differentiable ℂ v ∧ (∀ z, v z ≠ 0) ∧ (∀ z, Φ.GenRd φ ε t (q z) (fun k => p k z) (v z)) ∧ (∀ z u, Φ.GenRd φ ε t (q z) (fun k => p k z) u → u = v z) ∧ ∀ z z' (a : K → Fin g → ℂ), q z' = q z → (∀ k, a k ∈ Φ.lat ∧ p k z' = p k z + a k) → v z' = v z * ∏ k, Φ.fac (a k) (p k z) ^ ε k := by
  intro S A _ _ L x0 g Φ Z K _ φ ε t ht N q p hq hp hqp
  have hL : L.L.IsLB := L.isLB
  have hJ : ∀ z, ∃ j : K → L.L.ι, ⊤ ≤ q z ⁻¹ᵁ LB.wchart L.L φ j := fun z => exists_chart L.L hL φ (q z)
  choose J hJ using hJ
  have hgen : ∀ z, Φ.GenRd φ ε t (q z) (fun k => p k z)
      (valAt' (q z) (LB.wchart L.L φ (J z)) (t.s (J z)).val / ∏ k, Φ.fr (J z k) (p k z) ^ ε k) :=
    fun z => genRd_of_chart Φ φ ε t ht (fun k => hqp z k) (hJ z)
  refine ⟨fun z => valAt' (q z) (LB.wchart L.L φ (J z)) (t.s (J z)).val / ∏ k, Φ.fr (J z k) (p k z) ^ ε k,
    ?_, ?_, hgen, fun z u hu => genRd_eq Φ φ ε t hu (hJ z), ?_⟩
  · intro z0
    have hO := (hq (LB.wchart L.L φ (J z0)) (t.s (J z0)).val).1
    have hz0 : z0 ∈ {z | ⊤ ≤ q z ⁻¹ᵁ LB.wchart L.L φ (J z0)} := hJ z0
    have hnum : DifferentiableAt ℂ (fun z => valAt' (q z) (LB.wchart L.L φ (J z0)) (t.s (J z0)).val) z0 :=
      ((hq (LB.wchart L.L φ (J z0)) (t.s (J z0)).val).2 z0 hz0).differentiableAt (hO.mem_nhds hz0)
    have hfac : ∀ k, DifferentiableAt ℂ (fun z => Φ.fr (J z0 k) (p k z) ^ ε k) z0 := fun k => by
      have hc := top_le_chart Φ φ (fun k => hqp z0 k) (hJ z0) k
      have hO' := (Φ.hol (L.L.U (J z0 k)) 1).1
      have hfr : DifferentiableAt ℂ (Φ.fr (J z0 k)) (p k z0) :=
        (Φ.fr_hol (J z0 k) (p k z0) hc).differentiableAt (hO'.mem_nhds hc)
      exact (hfr.comp z0 ((hp k) z0)).zpow (Or.inl (Φ.fr_ne _ _ hc))
    have hden := differentiableAt_prod (Finset.univ : Finset K) (fun k z => Φ.fr (J z0 k) (p k z) ^ ε k) z0 hfac
    have hne := prod_fr_ne Φ φ ε (fun k => hqp z0 k) (hJ z0)
    have hinv : DifferentiableAt ℂ (fun z => (∏ k, Φ.fr (J z0 k) (p k z) ^ ε k)⁻¹) z0 := hden.inv hne
    have hw : DifferentiableAt ℂ (fun z => valAt' (q z) (LB.wchart L.L φ (J z0)) (t.s (J z0)).val /
        ∏ k, Φ.fr (J z0 k) (p k z) ^ ε k) z0 := by
      simpa only [div_eq_mul_inv, Pi.mul_def] using hnum.mul hinv
    refine hw.congr_of_eventuallyEq (Filter.eventually_of_mem (hO.mem_nhds hz0) fun z hz => ?_)
    exact genRd_eq Φ φ ε t (hgen z) hz
  · intro z
    exact div_ne_zero (valAt'_unit_val_ne_zero _ _ (hJ z) _) (prod_fr_ne Φ φ ε (fun k => hqp z k) (hJ z))
  · intro z z' a hzz ha
    have hz' : ⊤ ≤ q z' ⁻¹ᵁ LB.wchart L.L φ (J z) := by
      rw [hzz]
      exact hJ z
    have hA := prod_fr_ne Φ φ ε (fun k => hqp z' k) hz'
    have hper : ∀ k, Φ.fr (J z k) (p k z) = Φ.fac (a k) (p k z) * Φ.fr (J z k) (p k z + a k) := fun k =>
      Φ.fr_per (a k) (ha k).1 (J z k) (p k z) (top_le_chart Φ φ (fun k => hqp z k) (hJ z) k)
    have hC := prod_fr_ne Φ φ ε (fun k => hqp z k) (hJ z)
    have hB : ∏ k, Φ.fac (a k) (p k z) ^ ε k ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_
      intro h0
      have h1 := Φ.fr_ne _ _ (top_le_chart Φ φ (fun k => hqp z k) (hJ z) k)
      rw [hper k, h0, zero_mul] at h1
      exact h1 rfl
    show valAt' (q z') (LB.wchart L.L φ (J z')) (t.s (J z')).val / ∏ k, Φ.fr (J z' k) (p k z') ^ ε k = _
    rw [genRd_eq Φ φ ε t (hgen z') hz', hzz]
    simp only [(ha _).2] at hA ⊢
    simp only [hper, mul_zpow, Finset.prod_mul_distrib]
    field_simp

end GlobalTheory.AnValGenRd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingCorrMulInv
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValGenCorr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem chart_iff {X Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (j : K → L.ι)
    (x : Sp ℂ ⟶ Z) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  constructor
  · intro h k p _
    have hp := h (Set.mem_univ p)
    exact Set.mem_iInter.1 hp k
  · intro h p _
    exact Set.mem_iInter.2 fun k => h k (Set.mem_univ p)

theorem exists_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (x : Sp ℂ ⟶ X) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i := by
  have h : x cpt ∈ (⨆ i, L.U i : X.Opens) := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i, ReciprocityTheory.ChartRestriction.G.PullbackSections.top_le_of_mem hi⟩

theorem corr_val {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (hc : LB.Gen.Corr L φ ε φ' ε' t t')
    (J : (Y ⟶ X) → L.ι) (p : Sp ℂ ⟶ Y) (hJ : ∀ ψ, ⊤ ≤ (p ≫ ψ) ⁻¹ᵁ L.U (J ψ)) :
    valAt' p (LB.wchart L φ fun k => J (φ k)) (t.s fun k => J (φ k)).val =
      valAt' p (LB.wchart L φ' fun k => J (φ' k)) (t'.s fun k => J (φ' k)).val := by
  have h1 := (chart_iff L φ (fun k => J (φ k)) p).2 fun k => hJ _
  have h2 := (chart_iff L φ' (fun k => J (φ' k)) p).2 fun k => hJ _
  have h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k)) :=
    fun z hz => ⟨h1 hz, h2 hz⟩
  have e0 := hc (fun k => J (φ k)) (fun k => J (φ' k)) (fun _ _ e => congrArg J e) (fun _ _ e => congrArg J e)
    (fun _ _ e => congrArg J e)
  have e := congrArg (fun u : Γ(Y, LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k))ˣ =>
    valAt' p _ u.val) e0
  exact (vtf_val_res p _ h _).symm.trans (e.trans (vtf_val_res p _ h _))

theorem val_inv {Z : Scheme.{0}} (p : Sp ℂ ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, V)ˣ) :
    valAt' p V (u⁻¹).val = (valAt' p V u.val)⁻¹ := by
  have e := vtf_valU p h u (-1)
  rwa [zpow_neg_one, zpow_neg_one] at e

open scoped Classical in
theorem prod_fibre {T K : Type} [Fintype K] (φ : K → T) (ε : K → ℤ) (f : T → ℂ) (s : Finset T)
    (hs : ∀ k, φ k ∈ s) (hf : ∀ ψ ∈ s, f ψ ≠ 0) :
    ∏ k, f (φ k) ^ ε k = ∏ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have key : ∀ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) =
      ∏ k, if φ k = ψ then f (φ k) ^ ε k else 1 := by
    intro ψ hψ
    have h : ∀ u : Finset K, f ψ ^ (∑ k ∈ u, if φ k = ψ then ε k else 0) =
        ∏ k ∈ u, if φ k = ψ then f (φ k) ^ ε k else 1 := by
      intro u
      induction u using Finset.induction_on with
      | empty => simp
      | insert a u ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (hf ψ hψ), ih]
        congr 1
        split_ifs with h
        · rw [h]
        · simp
    exact h _
  rw [Finset.prod_congr rfl key, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]

theorem genRd_corr_mul_inv : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (φ' : K' → (Z ⟶ A.left)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (t' : LB.Gen (LB.LinComb L.L φ' ε')) (q : Sp ℂ ⟶ Z) (p : K → Fin g → ℂ) (p' : K' → Fin g → ℂ) (v v' : ℂ), Φ.GenRd φ ε t q p v → Φ.GenRd φ' ε' t' q p' v' → (LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι, (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧ v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k) ∧ (LB.Gen.Corr L.L φ ε φ' ε' t t' → LB.SameSum φ ε φ' ε' → (∃ π : (Z ⟶ A.left) → Fin g → ℂ, (∀ k, p k = π (φ k)) ∧ ∀ k, p' k = π (φ' k)) → v = v') ∧ Φ.GenRd (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' t t') q (Sum.elim p p') (v * v') ∧ Φ.GenRd φ (fun k => -ε k) (LB.invGen L.L φ ε t) q p v⁻¹ := by
  classical
  intro S A _ _ L x0 g Φ Z K K' _ _ φ ε φ' ε' t t' q p p' v v' h h'
  have hA : LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι,
      (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧
      v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k := by
    intro hc
    choose J hJ using fun ψ : Z ⟶ A.left => exists_chart L.L L.isLB (q ≫ ψ)
    refine ⟨J, hJ, ?_⟩
    have e := corr_val L.L φ ε φ' ε' t t' hc J q hJ
    have e1 := h.2 (fun k => J (φ k)) ((chart_iff L.L φ _ q).2 fun k => hJ _)
    have e2 := h'.2 (fun k => J (φ' k)) ((chart_iff L.L φ' _ q).2 fun k => hJ _)
    exact e1.symm.trans (e.trans e2)
  refine ⟨hA, ?_, ⟨?_, ?_⟩, ⟨h.1, ?_⟩⟩
  · rintro hc hs ⟨π, hπ, hπ'⟩
    obtain ⟨J, hJ, e⟩ := hA hc
    have n1 : ∀ k, Φ.fr (J (φ k)) (π (φ k)) ≠ 0 := fun k => by
      rw [← hπ k]; apply Φ.fr_ne; rw [← h.1 k]; exact hJ _
    have n2 : ∀ k, Φ.fr (J (φ' k)) (π (φ' k)) ≠ 0 := fun k => by
      rw [← hπ' k]; apply Φ.fr_ne; rw [← h'.1 k]; exact hJ _
    let s : Finset (Z ⟶ A.left) := Finset.univ.image φ ∪ Finset.univ.image φ'
    have hf : ∀ ψ ∈ s, Φ.fr (J ψ) (π ψ) ≠ 0 := by
      intro ψ hψ
      rcases Finset.mem_union.1 hψ with hψ | hψ
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n1 k
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n2 k
    have p1 := prod_fibre φ ε (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p2 := prod_fibre φ' ε' (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p3 : ∏ k, Φ.fr (J (φ k)) (π (φ k)) ^ ε k = ∏ k, Φ.fr (J (φ' k)) (π (φ' k)) ^ ε' k := by
      refine p1.trans (Eq.trans ?_ p2.symm)
      refine Finset.prod_congr rfl fun ψ _ => ?_
      congr 1
      exact hs ψ
    simp only [hπ, hπ'] at e
    rw [p3] at e
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (n2 k)) e
  · rintro (k | k)
    · exact h.1 k
    · exact h'.1 k
  · intro j hj
    have hj0 := (chart_iff L.L _ j q).1 hj
    have e1 := h.2 (j ∘ Sum.inl) ((chart_iff L.L φ _ q).2 fun k => hj0 (Sum.inl k))
    have e2 := h'.2 (j ∘ Sum.inr) ((chart_iff L.L φ' _ q).2 fun k => hj0 (Sum.inr k))
    refine (ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul q _ _ _).trans ?_
    refine (congrArg₂ (· * ·) ((vtf_val_res q _ hj _).trans e1) ((vtf_val_res q _ hj _).trans e2)).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  · intro j hj
    have e1 := h.2 j hj
    have e2 := val_inv q hj (t.s j)
    refine e2.trans ?_
    refine (congrArg (·⁻¹) e1).trans ?_
    simp only [mul_inv, zpow_neg, Finset.prod_inv_distrib]

end GlobalTheory.AnValGenCorr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingPullbackPeriodRigid
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.genMove_e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).2 Φ.lat.zero_mem

theorem AnFr.genMove_e_zero_left : (Φ.e 0).left = x0 ≫ eSec A := by
  rw [Φ.genMove_e_zero]
  show (toUnit (Over.mk x0) ≫ η[A]).left = _
  rw [Over.comp_left]
  rfl

theorem AnFr.genMove_e_per (z a : Fin g → ℂ) (ha : a ∈ Φ.lat) : Φ.e (z + a) = Φ.e z := by
  rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]

theorem genMove_chart {X Z : Scheme.{0}} (M : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z)
    (j : K → M.ι) (h : ⊤ ≤ q ⁻¹ᵁ LB.wchart M φ j) (k : K) : ⊤ ≤ (q ≫ φ k) ⁻¹ᵁ M.U (j k) :=
  fun _ hy => LB.wchart_le M φ j k (h hy)

theorem AnFr.genRd_pullGen_iff {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) {Z' : Scheme.{0}} (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ) :
    Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v := by
  have hc : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) ↔
      ⊤ ≤ (q ≫ h) ⁻¹ᵁ LB.wchart L.L φ j := fun j =>
    ⟨fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k,
      fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k⟩
  have hv : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) →
      valAt' q (LB.wchart L.L (fun k => h ≫ φ k) j) ((LB.pullGen L.L φ ε t h).s j).val =
        valAt' (q ≫ h) (LB.wchart L.L φ j) (t.s j).val := fun j hp =>
    (vtf_val_res q _ hp _).trans (vtf_val_pullU _ _ _ _)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [Category.assoc]; exact h1 k, fun j hj => ?_⟩
    exact (hv j ((hc j).2 hj)).symm.trans (h2 j ((hc j).2 hj))
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [← h1 k, Category.assoc], fun j hj => ?_⟩
    exact (hv j hj).trans (h2 j ((hc j).1 hj))

theorem AnFr.genRd_period {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ) (ha : ∀ k, a k ∈ Φ.lat)
    (H : Φ.GenRd φ ε t q p v) :
    Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k) := by
  obtain ⟨h1, h2⟩ := H
  refine ⟨fun k => by rw [Φ.genMove_e_per _ _ (ha k)]; exact h1 k, fun j hj => ?_⟩
  rw [h2 j hj, _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk := genMove_chart L.L φ q j hj k
  rw [h1 k] at hk
  rw [Φ.fr_per (a k) (ha k) (j k) (p k) hk, mul_zpow]
  rfl

theorem AnFr.genRd_rigPow (k : ℤ) :
    Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 := by
  refine ⟨fun _ => Φ.genMove_e_zero_left.symm, fun j hj => ?_⟩
  have hk := genMove_chart L.L (K := PUnit) (fun _ => eSec A) x0 j hj PUnit.unit
  rw [← Φ.genMove_e_zero_left] at hk
  rw [_root_.one_mul, Fintype.prod_unique]
  have e := Φ.fr_0 (j PUnit.unit) hk
  show _ = Φ.fr (j PUnit.unit) 0 ^ k
  rw [e]
  exact vtf_valU x0 hj (L.rig.s j) k

end

theorem genRd_pull_period_rig : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), (∀ (Z' : Scheme.{0}) (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ), Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v) ∧ (∀ (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ), (∀ k, a k ∈ Φ.lat) → Φ.GenRd φ ε t q p v → Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k)) ∧ ∀ k : ℤ, Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 :=
  fun _ _ _ _ _ _ _ Φ _ _ _ φ ε t =>
    ⟨fun _ h q p v => Φ.genRd_pullGen_iff φ ε t h q p v,
      fun q p a v ha H => Φ.genRd_period φ ε t q p a v ha H, fun k => Φ.genRd_rigPow k⟩

end GlobalTheory.AnVal
end
end

