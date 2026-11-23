module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartX
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem one_left'' {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] :
    (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  show (toUnit X ≫ η[M]).left = _
  rw [Over.comp_left]
  congr 1

def anE (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) :
    (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left) :=
  fun z => (F.ex i P z).left

theorem anHol (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) : IsHolFam (anE F i P) := by
  have hper : IsHolPeriods (F.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have h2 := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ hper).2
  intro U f
  obtain ⟨ho, hd⟩ := h2 U f
  have hι : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  have hc := hd.comp hι.differentiableOn (Set.mapsTo_preimage _ _)
  refine ⟨?_, ?_⟩
  · convert ho.preimage hι.continuous using 1
    ext z
    simp [anE]
  · convert hc using 1
    all_goals
      ext z
      simp [anE]

variable [Algebra c.F ℂ]

variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)


theorem basis_single (e' : Fin g ≃ Lt1 Dw) (v : Fin g → ℂ) :
    ∃! a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = v j := by
  have key : ∀ a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = a (e' j) := by
    intro a j
    rw [Fintype.sum_eq_single (e' j)]
    · simp
    · intro ℓ hℓ
      have hne : j ≠ e'.symm ℓ := by
        intro h
        apply hℓ
        rw [h, Equiv.apply_symm_apply]
      simp [hne]
  refine ⟨fun ℓ => v (e'.symm ℓ), fun j => ?_, fun a ha => ?_⟩
  · rw [key]
    simp
  · funext ℓ
    have h1 := ha (e'.symm ℓ)
    rw [key, Equiv.apply_symm_apply] at h1
    exact h1

def anAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Fin g → MvPowerSeries (Fin 1 × Fin g) ℂ :=
  fun k => MvPowerSeries.C (ty k (a : E)) * MvPowerSeries.X ((0 : Fin 1), k)

theorem jetSubstP_anAct (m : ℕ) (a : 𝓞 E) (b : Jet ℂ (Fin 1 × Fin g) m) :
    jetSubstP m (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) b =
      jetScaleP m (fun k => ty k (a : E)) b := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  unfold jetSubstP jetScaleP
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk]
  have key : ∀ p : Fin 1 × Fin g,
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (psTrunc m (anAct ty a p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2)))) =
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (MvPolynomial.C (ty p.2 (a : E)) * MvPolynomial.X p) := by
    rintro ⟨i, k⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    set q : Fin 1 × Fin g := ((0 : Fin 1), k) with hq
    have hps : psTrunc m (anAct ty a k) =
        if Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) then
          MvPolynomial.C (ty k (a : E)) * MvPolynomial.X q else 0 := by
      unfold psTrunc anAct
      by_cases hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ))
      · rw [if_pos hmem, Finset.sum_eq_single (Finsupp.single q 1)]
        · simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, MvPolynomial.C_mul_X_eq_monomial, hq]
        · intro e _ he
          simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, he]
        · intro h
          exact absurd hmem h
      · rw [if_neg hmem]
        apply Finset.sum_eq_zero
        intro e he
        have hne : e ≠ Finsupp.single q 1 := fun h => hmem (h ▸ he)
        simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, hne]
    rw [hps]
    by_cases hm0 : m = 0
    · subst hm0
      have hnot : Finsupp.single q 1 ∉ (degLE 0 : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        intro hmem
        rw [degLE, Finset.mem_filter] at hmem
        have := hmem.2
        rw [Finsupp.sum_single_index rfl] at this
        omega
      rw [if_neg hnot]
      simp only [map_zero, sub_zero]
      symm
      rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
    · have hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        rw [degLE, Finset.mem_filter, Finsupp.sum_single_index rfl]
        refine ⟨Finset.mem_image.2 ⟨fun j => if j = q then ⟨1, by omega⟩ else 0, Finset.mem_univ _, ?_⟩, by omega⟩
        ext j
        by_cases hj : j = q
        · subst hj
          simp
        · simp [hj, Finsupp.single_apply, Ne.symm hj]
      rw [if_pos hmem]
      simp [MvPolynomial.constantCoeff_X, hq]
  show (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f) = (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
  congr 2
  funext p
  exact key p

theorem fst_jetTan (ℓ : Fin 1 × Fin g) (a : Jet ℂ (Fin 1 × Fin g) (0 + 1)) :
    ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) a).fst =
      (jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [jetTan, jetAug, liftJet]
  try simp only [Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
  try simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
  induction p using MvPolynomial.induction_on with
  | C r => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = ℓ <;> simp [hj, hp]

theorem epsMul_algebraMap (cc : ℂ) (a : ℂ) : epsMul cc (algebraMap ℂ (DualNumber ℂ) a) = algebraMap ℂ _ a := by
  ext <;> simp [epsMul]

def epsHom (x : Sp ℂ ⟶ Xo.X) (cc : ℂ) : tEps x ⟶ tEps x :=
  Over.homMk (spMap (epsMul cc)) (by
    show spMap (epsMul cc) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x
    rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun a => epsMul_algebraMap cc a)

theorem spMap_epsMul_zero_jetTan (ℓ : Fin 1 × Fin g) :
    spMap (epsMul (0 : ℂ)) ≫ spMap ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
  have h : (epsMul (0 : ℂ)).comp ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) = (algebraMap ℂ (DualNumber ℂ)).comp
      ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · simp [epsMul, fst_jetTan, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem epsMul_one : epsMul (1 : ℂ) = RingHom.id (DualNumber ℂ) := by
  ext x <;> simp [epsMul]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ComposeLinearAction
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ NumberField

section Ev

variable {g m n : ℕ}

theorem ev_addF (a : Fin 2 → Pt ℂ n g) (ha : ∀ p : Fin 2 × Fin g, constantCoeff (a p.1 p.2) = 0) (i : Fin g) :
    ev a (addF ℂ g i) = a 0 i + a 1 i := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  simp only [ev, addF]
  rw [MvPowerSeries.subst_add hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]

theorem ev_CX (a : Fin 1 → Pt ℂ n g) (ha : ∀ p : Fin 1 × Fin g, constantCoeff (a p.1 p.2) = 0) (c : ℂ)
    (i : Fin g) : ev a (C c * X ((0 : Fin 1), i) : PS ℂ 1 g) = C c * a 0 i := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul]
  simp only [ev]
  rw [MvPowerSeries.subst_smul hs, MvPowerSeries.subst_X hs]

theorem addOf_addF (a b : Pt ℂ n g) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    addOf (addF ℂ g) a b = a + b := by
  funext i
  simp only [addOf]
  rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [ha, hb])]
  simp

theorem expS_zero_an (k : Type) [CommRing k] [Algebra ℚ k] {n d : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  have ha : PowerSeries.HasSubst (0 : PS k n d) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  unfold FB.expS
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (PowerSeries.exp k)]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, zero_mul, zero_add,
    PowerSeries.constantCoeff_exp, map_one, ← PowerSeries.coe_substAlgHom ha, map_one]

theorem cc_pt (j : Fin n) (i : Fin g) : constantCoeff (pt ℂ g j i) = 0 := by
  simp [pt]

end Ev

def addFGLaw (g : ℕ) : FGLaw ℂ g where
  F := addF ℂ g
  const i := by simp [addF]
  unit i := by
    rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt]
  comm i := by
    rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, addF, add_comm]
  assoc i := by
    have h01 : (fun l => ev (n := 3) ![pt ℂ g 0, pt ℂ g 1] (addF ℂ g l)) =
        fun l => (X ((0 : Fin 3), l) + X ((1 : Fin 3), l) : PS ℂ 3 g) :=
      funext fun l => by rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    have h12 : (fun l => ev (n := 3) ![pt ℂ g 1, pt ℂ g 2] (addF ℂ g l)) =
        fun l => (X ((1 : Fin 3), l) + X ((2 : Fin 3), l) : PS ℂ 3 g) :=
      funext fun l => by rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    rw [h01, h12, ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt]),
      ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, add_assoc]

section Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}

def linAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Pt ℂ 1 g :=
  fun k => C (ty k (a : E)) * X ((0 : Fin 1), k)

theorem cc_linAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (i : Fin g) : constantCoeff (linAct ty a i) = 0 := by
  simp [linAct]

theorem compose_linear_action (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (b : Pt ℂ n g) (hb : ∀ i, constantCoeff (b i) = 0) :
    comp1 (linAct ty a) b = fun i => C (ty i (a : E)) * b i := by
  funext i
  simp only [comp1, linAct]
  rw [ev_CX _ (fun ⟨j, k⟩ => by fin_cases j; simp [hb])]
  simp

def linOAct (ty : Fin g → (E →+* ℂ)) : OAct (𝓞 E) (addFGLaw g) where
  act := linAct ty
  const := cc_linAct ty
  hom a := by
    show comp1 (linAct ty a) (addOf (addF ℂ g) (pt ℂ g 0) (pt ℂ g 1)) =
      addOf (addF ℂ g) (comp1 (linAct ty a) (pt ℂ g 0)) (comp1 (linAct ty a) (pt ℂ g 1))
    rw [addOf_addF _ _ (cc_pt 0) (cc_pt 1), compose_linear_action _ _ _ (fun i => by simp [pt]),
      compose_linear_action _ _ _ (cc_pt 0), compose_linear_action _ _ _ (cc_pt 1), addOf_addF _ _ (fun i => by simp [pt])
        (fun i => by simp [pt])]
    funext i
    simp [mul_add]
  add_act a b := by
    show linAct ty (a + b) = addOf (addF ℂ g) (linAct ty a) (linAct ty b)
    rw [addOf_addF _ _ (cc_linAct ty a) (cc_linAct ty b)]
    funext i
    simp [linAct, add_mul]
  mul_act a b := by
    show linAct ty (a * b) = comp1 (linAct ty a) (linAct ty b)
    rw [compose_linear_action _ _ _ (cc_linAct ty b)]
    funext i
    simp [linAct, mul_assoc]
  one_act := by
    funext i
    simp [linAct, pt]

def anFB [StarRing (𝓞 E)] (ty : Fin g → (E →+* ℂ)) : FB ℂ g (𝓞 E) := FB.triv (addFGLaw g) (linOAct ty)

theorem anFB_canon [StarRing (𝓞 E)] (ty : Fin g → (E →+* ℂ)) : (anFB ty).IsCanonGauge ℂ 0 := by
  constructor <;> simp [anFB, FB.triv, ev_zero', expS_zero_an]

end Act

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

