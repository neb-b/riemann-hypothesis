module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AbelianHolomorphicFrameReadingConstOfFormsCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnVal.genRd_const : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (Λ : K → (Fin N → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Ga : AddSubgroup (Fin N → ℂ)), IsHolFam q → (∀ z k, q z ≫ φ k = (Φ.e (Λ k z)).left) → Submodule.span ℝ (Ga : Set (Fin N → ℂ)) = ⊤ → (∀ gm ∈ Ga, (∀ z, q (z + gm) = q z) ∧ ∀ k, Λ k gm ∈ Φ.lat) → (∀ z w, ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k w) = 0) → (∃ v : ℂ, v ≠ 0 ∧ ∀ z, Φ.GenRd φ ε t (q z) (fun k => Λ k z) v) ∧ ∀ gm ∈ Ga, ∏ k, Φ.χ (Λ k gm) ^ ε k = 1 := by
  intro S A _ _ L x0 g Φ Z K _ φ ε t ht N q Λ Ga hq hqe hspan hper hH
  obtain ⟨v, hv, hv0, hrd, -, hfac⟩ := _root_.GlobalTheory.AnValGenRd.exists_reading S A L x0 g Φ Z K φ ε t ht N q (fun k z => Λ k z) hq
    (fun k => (LinearMap.toContinuousLinearMap (Λ k)).differentiable) hqe
  have hprod : ∀ gm z, ∏ k, Φ.fac (Λ k gm) (Λ k z) ^ ε k = ∏ k, Φ.χ (Λ k gm) ^ ε k := by
    intro gm z
    simp only [AnFr.fac, mul_zpow, Finset.prod_mul_distrib, ← Complex.exp_int_mul, ← Complex.exp_sum]
    have h : ∑ k, (ε k : ℂ) * (Real.pi * hermForm Φ.Hm (Λ k z) (Λ k gm) +
        Real.pi / 2 * hermForm Φ.Hm (Λ k gm) (Λ k gm)) =
        Real.pi * ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k gm) +
        Real.pi / 2 * ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k gm) (Λ k gm) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h, hH, hH]
    simp
  have hstep : ∀ gm ∈ Ga, ∀ z, v (z + gm) = v z * ∏ k, Φ.χ (Λ k gm) ^ ε k := by
    intro gm hgm z
    rw [← hprod gm z]
    exact hfac z (z + gm) (fun k => Λ k gm) ((hper gm hgm).1 z)
      (fun k => ⟨(hper gm hgm).2 k, map_add _ _ _⟩)
  have hnorm : ∀ gm ∈ Ga, ∀ z, ‖v (z + gm)‖ = ‖v z‖ := by
    intro gm hgm z
    rw [hstep gm hgm z, norm_mul, norm_prod]
    have : ∀ k, ‖Φ.χ (Λ k gm) ^ ε k‖ = 1 := fun k => by
      rw [norm_zpow, Φ.χ_norm _ ((hper gm hgm).2 k), one_zpow]
    simp [this]
  have hconst : ∀ z, v z = v 0 := by
    intro z
    refine norm_periodic_const_range Ga.subtype ?_ v hv (fun z a => hnorm a a.2 z) z 0
    simpa using hspan
  refine ⟨⟨v 0, hv0 0, fun z => hconst z ▸ hrd z⟩, fun gm hgm => ?_⟩
  have h := hstep gm hgm 0
  rw [hconst] at h
  exact (mul_eq_left₀ (hv0 0)).1 h.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameExponentialJetsIsChart
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal

attribute [local instance] Over.cartesianMonoidalCategory

theorem chart_isHolFam_comp_clm {Y : Scheme.{0}} {g N : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (A : (Fin N → ℂ) →L[ℂ] (Fin g → ℂ)) : IsHolFam fun v => e (A v) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage A.continuous, h2.comp A.differentiable.differentiableOn fun _ hv => hv⟩

theorem chart_holTo_of_isHolFam {Y : Scheme.{0}} {N : ℕ} {e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolFam e) :
    IsHolTo Set.univ e := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  simp only [Set.mem_univ, true_and]
  exact ⟨h1, h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem AnPt.chart_jx_left (m : ℕ) : (Φ.jx m).left = jetPt (fun z => (Φ.e z).left) Φ.hol m := rfl

theorem AnPt.chart_e_zero : Φ.e 0 = 1 := by
  have h := Φ.e_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem AnPt.chart_trunc (m : ℕ) :
    homAt y.x (jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) ≫ Φ.jx (m + 1) =
      Φ.jx m := by
  ext1
  rw [Over.comp_left, Φ.chart_jx_left, Φ.chart_jx_left]
  exact jetPt_trunc _ _ m

theorem AnPt.chart_zero (m : ℕ) :
    homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) ≫ Φ.jx m = 1 := by
  ext1
  rw [Over.comp_left, Φ.chart_jx_left, one_left'']
  have h1 := jetPt_aug (fun z => (Φ.e z).left) Φ.hol m
  refine h1.trans ?_
  show (Φ.e 0).left = _
  rw [Φ.chart_e_zero, one_left'']
  show y.x ≫ _ = (spMap (algebraMap ℂ ℂ) ≫ y.x) ≫ _
  rw [Algebra.algebraMap_self, spMap]
  simp

theorem AnPt.chart_act (m : ℕ) (a : 𝓞 E) :
    Φ.jx m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) ≫ Φ.jx m := by
  ext1
  rw [Over.comp_left, Over.comp_left, Φ.chart_jx_left]
  have hlin : ∀ z, (Φ.e z).left ≫ (Xo.univ.t.act.act a).left = (Φ.e (fun k => ty k (a : E) * z k)).left := by
    intro z
    rw [← Over.comp_left, ← Φ.lin a z]
    rfl
  have hol' := isHolFam_comp (fun z => (Φ.e z).left) Φ.hol (Xo.univ.t.act.act a).left
  rw [jetPt_comp (fun z => (Φ.e z).left) Φ.hol _ _ hol' (fun z => rfl)]
  haveI : IsLocalHom ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
        Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) :=
    isLocalHom_jetMap (m := m)
      (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) -
        MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2))))
      (fun _ => sub_const_mem_orig _)
  symm
  refine jetPt_precomp (fun z => (Φ.e z).left) _ Φ.hol hol' ?_ m _ ?_
  · show (Φ.e 0).left ≫ _ = (Φ.e 0).left
    rw [hlin]; congr 2; funext k; simp
  · intro U hU f
    change jetSubstP m _ (jetOf m _) = _
    rw [jetSubstP_anAct, ← jetOf_scale m _ (contDiffAt_val _ Φ.hol hU f)]
    congr 1
    funext z
    show valAt' (Φ.e _).left U f = valAt' ((Φ.e z).left ≫ _) U f
    rw [hlin]

theorem AnPt.chart_tan (j0 : Fin g) (vt : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)
    (hd : IsDerivAt0 (fun z => (Φ.e z).left) (Pi.single j0 1) vt) :
    IsCombAt y.x (m := g)
      (fun j => (homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫
        Φ.jx (0 + 1)).left) (fun j => if j = j0 then 1 else 0) vt := by
  classical
  let v : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j =>
    homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫ Φ.jx (0 + 1)
  let u : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j => epsHom y.x (if j = j0 then 1 else 0) ≫ v j
  refine ⟨u, fun j => by simp [u, v, epsHom], ?_⟩
  have hone : ∀ j, j ≠ j0 → u j = 1 := by
    intro j hj
    ext1
    simp only [u, v, if_neg hj, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left]
    rw [← Category.assoc, spMap_epsMul_zero_jetTan, Category.assoc, jetPt_aug, one_left'']
    show spMap _ ≫ (Φ.e 0).left = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y.x) ≫ _
    rw [Φ.chart_e_zero, one_left'', Category.assoc]
    rfl
  have hprod : (List.ofFn u).prod = u j0 := by
    rw [List.prod_ofFn, Finset.prod_eq_single j0 (fun j _ hj => hone j hj) (by simp)]
  rw [hprod]
  simp only [u, v, if_pos rfl, ite_true, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left,
    epsMul_one]
  rw [show spMap (RingHom.id (DualNumber ℂ)) = 𝟙 _ from by simp [spMap]]
  exact (Category.id_comp _).trans (jetPt_tan (fun z => (Φ.e z).left) Φ.hol ((0 : Fin 1), j0) vt hd)

theorem AnPt.chart_pair : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (Φ.e (anPr 0 v)).left (Φ.e (anPr 1 v)).left
        ((Over.w (Φ.e (anPr 0 v))).trans (Over.w (Φ.e (anPr 1 v))).symm) :=
  chart_holTo_of_isHolFam (isHolFam_pullback_lift _ _ _ Xo.univ.t.G.hom Xo.univ.t.G.hom (2 * g)
    (fun v => (Φ.e (anPr 0 v)).left) (fun v => (Φ.e (anPr 1 v)).left) y.x
    (fun v => Over.w (Φ.e (anPr 0 v))) (fun v => Over.w (Φ.e (anPr 1 v)))
    (chart_isHolFam_comp_clm _ Φ.hol (anPr 0)) (chart_isHolFam_comp_clm _ Φ.hol (anPr 1)))

theorem AnPt.chart_law (m : ℕ) :
    homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) ≫ Φ.jx m =
      jpt y g Φ.jx m (0 : Fin 2) * jpt y g Φ.jx m (1 : Fin 2) :=
  jets_law y.x Φ.e Φ.hol Φ.jx (fun _ => rfl) Φ.e_add Φ.chart_pair m

theorem anPt_isChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el),
    IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec el) Φ.jx :=
  fun _ _ _ _ _ _ _ _ _ _ _ y _ _ el Φ =>
    { zero := fun m => Φ.chart_zero m
      trunc := fun m => Φ.chart_trunc m
      law := fun m => Φ.chart_law m
      act := fun m a => Φ.chart_act m a
      tan := fun ℓ => Φ.chart_tan (el.symm ℓ) (y.u ℓ.1 ℓ.2) (Φ.der ℓ)
      basis := fun v => basis_single el v }

end GlobalTheory.AnVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJets
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal

attribute [local instance] Over.cartesianMonoidalCategory

theorem isHolFam_precomp_clm {Y : Scheme.{0}} {g N : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (A : (Fin N → ℂ) →L[ℂ] (Fin g → ℂ)) : IsHolFam (fun v => e (A v)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage A.continuous, h2.comp A.differentiable.differentiableOn fun _ hv => hv⟩

def colPr (n g : ℕ) (i : Fin n) : (Fin (n * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) (finProdFinEquiv (i, j))

theorem colPr_apply (n g : ℕ) (i : Fin n) (v : Fin (n * g) → ℂ) (j : Fin g) :
    colPr n g i v j = v (finProdFinEquiv (i, j)) := rfl

theorem anLin_colPr (n g : ℕ) (i : Fin n) (p : Fin 1 × Fin g) :
    anLin (colPr n g i) p = MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, p.2)) := by
  rw [anLin, Finset.sum_eq_single (finProdFinEquiv (i, p.2))]
  · rw [colPr_apply, Pi.single_eq_same, map_one, _root_.one_mul]
  · intro k _ hk
    simp [colPr_apply, Ne.symm hk]
  · simp

theorem renN_colPr (n g m : ℕ) (i : Fin n) (a : Jet ℂ (Fin 1 × Fin g) m) :
    renN n g m (jetMap (anLin (colPr n g i)) (anLin_mem _) a) = jetCopy (S := ℂ) g m i a := by
  unfold renN jetCopy
  exact anJetMap_comp _ _ _ _ _ _
    (fun p => by simp only [anLin_colPr, MvPolynomial.aeval_X, Equiv.symm_apply_apply]) a

theorem jetCopy_one_zero (g m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) : jetCopy (S := ℂ) g m (0 : Fin 1) a = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun q : Fin 1 × Fin g =>
    (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) p) = _
  have h : (fun q : Fin 1 × Fin g => (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) =
      MvPolynomial.X := by
    funext q
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h, MvPolynomial.aeval_X_left_apply]

theorem spMap_jetCopy_jetPt {Y : Scheme.{0}} {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (n m : ℕ) (i : Fin n) :
    spMap (jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt e hol m =
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt (fun v => e (colPr n g i v)) (isHolFam_precomp_clm e hol _) m := by
  have hring : ((jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) =
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m).comp
        ((jetMap (anLin (colPr n g i)) (anLin_mem _) :
          Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (n * g)) m) :
          Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) :=
    RingHom.ext fun a => (renN_colPr n g m i a).symm
  rw [hring, anSpMap_comp, Category.assoc]
  congr 1
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin (colPr n g i)) (anLin_mem _)
  refine jetPt_precompD _ _ hol _ (by show e (colPr n g i 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) (colPr n g i)).symm

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).mpr Φ.lat.zero_mem

theorem AnFr.jetMap_copy (n m : ℕ) (i : Fin n) :
    Φ.JetMap m (homAt x0 (jetCopy (S := ℂ) g m i) ≫ anJX x0 Φ.e Φ.hol m).left (LinearMap.proj i) :=
  ⟨isHolFam_precomp_clm _ Φ.hol (colPr n g i), spMap_jetCopy_jetPt _ Φ.hol n m i⟩

theorem AnFr.jetMap_self (m : ℕ) :
    Φ.JetMap (n := 1) m (anJX x0 Φ.e Φ.hol m).left (LinearMap.proj 0) := by
  refine ⟨isHolFam_precomp_clm _ Φ.hol (colPr 1 g 0), ?_⟩
  have h := spMap_jetCopy_jetPt _ Φ.hol 1 m 0
  have hid : (jetCopy (S := ℂ) g m (0 : Fin 1) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) =
      RingHom.id _ := RingHom.ext (jetCopy_one_zero g m)
  rw [hid, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at h
  exact h

theorem AnFr.jetMap_one (n m : ℕ) :
    Φ.JetMap m (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A).left 0 := by
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left =
      (1 : Over.mk x0 ⟶ A).left := fun v => by rw [LinearMap.zero_apply, Φ.e_zero]
  have hf := funext hc
  have hol : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left) := by
    rw [hf]; exact isHolFam_const _
  refine ⟨hol, ?_⟩
  have h1 := jetPt_comp _ (isHolFam_const (g := n * g) (1 : Over.mk x0 ⟶ A).left) (𝟙 _) _ hol
    (fun v => (Category.comp_id _).trans (hc v).symm) m
  rw [← h1, Category.comp_id, ← jetPt_const, ← Category.assoc, spMap_comp_alg]
  let k : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ Over.mk x0 :=
    Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin n × Fin g) m))) rfl
  have hk : (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A) = k ≫ (1 : Over.mk x0 ⟶ A) := (MonObj.comp_one k).symm
  rw [hk]
  rfl

theorem AnFr.jetMap_comp {n m : ℕ} (a : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hT : ∀ z, Φ.e (T z) = Φ.e z ≫ φ) (ha : Φ.JetMap m a.left Λ) : Φ.JetMap m (a ≫ φ).left (T ∘ₗ Λ) := by
  obtain ⟨hol, ha⟩ := ha
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e (Λ (colsOf n g v))).left ≫ φ.left =
      (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left := fun v => by
    rw [LinearMap.comp_apply, hT, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hol _
  refine ⟨hol', ?_⟩
  rw [Over.comp_left, ha, Category.assoc, jetPt_comp _ hol _ _ hol' hc]

theorem AnFr.jetMap_pair {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left),
      (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt _ hq m := by
  obtain ⟨hola, ha⟩ := ha
  obtain ⟨holb, hb⟩ := hb
  have hq : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left) :=
    GlobalTheory.AnVal.isHolFam_pullback_lift S A.left A.left A.hom A.hom (n * g) _ _ x0 (fun v => Over.w (Φ.e (Λ (colsOf n g v))))
      (fun v => Over.w (Φ.e (Λ' (colsOf n g v)))) hola holb
  refine ⟨hq, ?_⟩
  have hf : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (fst A A).left = (Φ.e (Λ (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_fst]
  have hs : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (snd A A).left = (Φ.e (Λ' (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_snd]
  apply pullback.hom_ext
  · show (lift a b).left ≫ (fst A A).left = (_ ≫ jetPt _ hq m) ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, Category.assoc, jetPt_comp _ hq _ _ hola hf, ha]
  · show (lift a b).left ≫ (snd A A).left = (_ ≫ jetPt _ hq m) ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, Category.assoc, jetPt_comp _ hq _ _ holb hs, hb]

theorem AnFr.jetMap_mul {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    Φ.JetMap m (a * b).left (Λ + Λ') := by
  obtain ⟨hq, hab⟩ := Φ.jetMap_pair a b Λ Λ' ha hb
  have hc : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (MonObj.mul : A ⊗ A ⟶ A).left = (Φ.e ((Λ + Λ') (colsOf n g v))).left := fun v => by
    rw [LinearMap.add_apply, Φ.e_add, CategoryTheory.Hom.mul_def, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((Λ + Λ') (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hq _
  refine ⟨hol', ?_⟩
  rw [CategoryTheory.Hom.mul_def, Over.comp_left, hab, Category.assoc, jetPt_comp _ hq _ _ hol' hc]

end General

theorem jetPts_jetMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (n m : ℕ), (∀ i : Fin n, Φ.toAnFr.JetMap m (jpt y g Φ.jx m i).left (LinearMap.proj i)) ∧ Φ.toAnFr.JetMap m (1 : jO y g m n ⟶ Xo.univ.t.G).left 0 ∧ (∀ (a b : jO y g m n ⟶ Xo.univ.t.G) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m b.left Λ' → Φ.toAnFr.JetMap m (a * b).left (Λ + Λ') ∧ ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left), (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m) ∧ (∀ (a : jO y g m n ⟶ Xo.univ.t.G) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (α : 𝓞 E), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m (a ≫ Xo.univ.t.act.act α).left (tyAct ty α ∘ₗ Λ)) ∧ Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ n m
  exact ⟨fun i => Φ.toAnFr.jetMap_copy n m i, Φ.toAnFr.jetMap_one n m,
    fun a b Λ Λ' ha hb => ⟨Φ.toAnFr.jetMap_mul a b Λ Λ' ha hb, Φ.toAnFr.jetMap_pair a b Λ Λ' ha hb⟩,
    fun a Λ α ha => Φ.toAnFr.jetMap_comp a Λ _ _ (Φ.lin α) ha, Φ.toAnFr.jetMap_self m⟩

end GlobalTheory.AnVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingPullbackPeriodRigidStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generatorReading_pullback_period_rigid : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), (∀ (Z' : Scheme.{0}) (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ), Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v) ∧ (∀ (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ), (∀ k, a k ∈ Φ.lat) → Φ.GenRd φ ε t q p v → Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k)) ∧ ∀ k : ℤ, Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 := by
  first | exact @GlobalTheory.AnVal.genRd_pull_period_rig | exact GlobalTheory.AnVal.genRd_pull_period_rig | (intros; apply GlobalTheory.AnVal.genRd_pull_period_rig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingTwistedPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reading_twisted_pullback : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A) (m : Over.mk x0 ⊗ A ⟶ A) (hm : ψ ≫ snd (Over.mk x0) A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L.L b (Over.mk x0))) (s' : LB.Sec (LPow A L.L a (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) (p : (Fin g → ℂ) → Fin g → ℂ) (v : (Fin g → ℂ) → ℂ), ψ ≫ fst (Over.mk x0) A = fst (Over.mk x0) A → IsTwistPull A L.L ψ m hm a b α s s' → Φ.Rd b s θ → (∀ z, (ptSecT A (Φ.e z)).left ≫ m.left = (Φ.e (p z)).left ∧ ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j ∧ valAt' (ptSecT A (Φ.e z)).left (LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j) (α.s j).val = v z * (Φ.fr (j 0) z ^ a * Φ.fr (j 1) (p z) ^ (-b))) → Φ.Rd a s' (fun z => v z * θ (p z)) := by
  first | exact @GlobalTheory.AnVal.AnFr.rd_twistPull | exact GlobalTheory.AnVal.AnFr.rd_twistPull | (intros; apply GlobalTheory.AnVal.AnFr.rd_twistPull <;> assumption)
end

