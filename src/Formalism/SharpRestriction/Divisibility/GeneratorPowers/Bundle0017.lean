module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieAlg
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0015

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.BidegreeTwoJet
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace BidegreeTwoJet

section Jets

variable {V : Type} [CommRing V] {G' G : Over (Sp V)} [GrpObj G'] [GrpObj G] {n d : ℕ}

def zV (pG : IsPowGrp G' G n) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) : jOG (𝟙 (Sp V)) d m n ⟶ G' :=
  pG.lim.lift (Fan.mk _ fun i => homAt (𝟙 (Sp V)) (jetCopy (S := V) d m i) ≫ xT m)

end Jets

section Coord

variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D' : DegData V I}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' G : Over (Sp V)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  {n d : ℕ}

end Coord


end BidegreeTwoJet
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ChartJetTanSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    letI := io.toAlgebra
    ∀ ℓ : Lt1 Dw, IsCombAt y.1.x
      (fun j : Fin d => (Formalism.L2.Pj.homAt y.1.x
        (jetTan ((0 : Fin 1), j) : Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) ≫ JetTr.xU I xT 1).left)
      (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) (y.1.u ℓ.1 ℓ.2)

def ChartJetBasisSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    ∀ v : Fin d → T.Fr, ∃! a : Lt1 Dw → T.Fr, ∀ j, ∑ ℓ, a ℓ * algebraMap T.V T.Fr (uvecT ℓ j) = v j

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrC
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  first
  | exact spMap_id R
  | exact spMap_id
  | simp [spMap]
  | unfold spMap

theorem spMap_alg_self (R : Type) [CommRing R] : spMap (algebraMap R R) = 𝟙 (Sp R) := by
  first
  | exact spMap_id' R
  | (rw [Algebra.algebraMap_self]; exact spMap_id' R)

theorem spMap_algHom_alg {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) : spMap (φ : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  first
  | (rw [← spMap_comp]; congr 1; exact φ.comp_algebraMap)
  | (rw [spMap_comp]; congr 1; exact φ.comp_algebraMap)
  | (simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])
  | unfold spMap

theorem jetCoef_substP {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) {κ κ' : Type} (m : ℕ)
    (φ : κ → MvPolynomial κ' V) :
    (jetCoef f κ' m).comp ((jetSubstP m φ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetSubstP m (fun i => MvPolynomial.map f (φ i)) : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by
  have keyV : ∀ (ψ : κ → MvPolynomial κ' V) (j : κ),
      (jetSubstP m ψ : Jet V κ m →ₐ[V] Jet V κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
        Ideal.Quotient.mk _ (ψ j - MvPolynomial.C (MvPolynomial.constantCoeff (ψ j))) := fun ψ j =>
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.bind₁_X_right _ j)
  have keyK : ∀ (ψ : κ → MvPolynomial κ' K) (j : κ),
      (jetSubstP m ψ : Jet K κ m →ₐ[K] Jet K κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
        Ideal.Quotient.mk _ (ψ j - MvPolynomial.C (MvPolynomial.constantCoeff (ψ j))) := fun ψ j =>
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.bind₁_X_right _ j)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro v
    have e2 : ∀ (κ'' : Type), jetCoef f κ'' m (algebraMap V (Jet V κ'' m) v) =
        algebraMap K (Jet K κ'' m) (f v) := by
      intro κ''
      show jetCoef f κ'' m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
      simp [jetCoef]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (Ideal.Quotient.mk (orig V κ ^ (m + 1))) (MvPolynomial.C v) = algebraMap V (Jet V κ m) v from rfl]
    rw [AlgHom.commutes, e2, e2, AlgHom.commutes]
  · intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [keyV φ i]
    have eX : jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.X i)) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
      simp [jetCoef]
    rw [eX, keyK]
    set_option synthInstance.maxHeartbeats 200000 in
      simp [jetCoef, MvPolynomial.constantCoeff_map]

theorem unit_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  obtain ⟨hpb, hmul⟩ := h
  let x₀ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) (by
    show (η[G'].left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w η[G']])
  have hη : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    show toUnit (𝟙_ (Over S')) ≫ η[G'] = η[G']
    first
    | rw [toUnit_unit, Category.id_comp]
    | rw [Subsingleton.elim (toUnit (𝟙_ (Over S'))) (𝟙 _), Category.id_comp]
  have h2 := hmul (𝟙_ (Over S')) η[G'] η[G'] x₀ x₀ rfl rfl
  have hidem : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, ← hη, _root_.one_mul]
    rfl
  have h1 : x₀ = 1 := by
    first
    | exact mul_eq_left.1 hidem
    | exact mul_right_eq_self.1 hidem
  have h3 : x₀.left = (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ η[G]).left :=
    congrArg (fun g => g.left) h1
  rw [Over.comp_left] at h3
  have h4 : (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f))).left = f := by
    first
    | simp
    | simpa using Over.w (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)))
  rw [h4] at h3
  exact h3

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

theorem xL_zero (hz : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetAug : Jet T.V (Fin 1 × Fin d) m →ₐ[T.V] T.V) ≫ xT m = 1)
    (m : ℕ) : spMap ((jetAug : Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] T.Fr) : Jet T.Fr (Fin 1 × Fin d) m →+* T.Fr) ≫
      xL I xT m = η[I.t'.G].left := by
  apply ext2 I
  · rw [Category.assoc, xL_fst, ← Category.assoc, spMap_comp', jetCoef_aug, ← spMap_comp', Category.assoc,
      unit_push I.m2.cart]
    have e := congrArg CommaMorphism.left (hz m)
    change spMap _ ≫ (xT m).left = (spMap (algebraMap T.V T.V) ≫ 𝟙 _) ≫ η[I.G.G].left at e
    rw [e, spMap_alg_self, Category.id_comp, Category.id_comp]
  · rw [Category.assoc, xL_snd, spMap_algHom_alg, spMap_alg_self, Over.w η[I.t'.G]]
    rfl

theorem xL_trunc (ht : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
      (jetTrunc : Jet T.V (Fin 1 × Fin d) (m + 1) →ₐ[T.V] Jet T.V (Fin 1 × Fin d) m) ≫ xT (m + 1) = xT m)
    (m : ℕ) : spMap ((jetTrunc : Jet T.Fr (Fin 1 × Fin d) (m + 1) →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
      Jet T.Fr (Fin 1 × Fin d) (m + 1) →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT (m + 1) = xL I xT m := by
  apply ext2 I
  · rw [Category.assoc, xL_fst, xL_fst, ← Category.assoc, spMap_comp', jetCoef_trunc, ← spMap_comp',
      Category.assoc]
    exact congrArg (spMap (jc (d := d) 1 m) ≫ ·) (congrArg CommaMorphism.left (ht m))
  · rw [Category.assoc, xL_snd, xL_snd, spMap_algHom_alg]

theorem xL_act (actT : Fin d → MvPowerSeries (Fin 1 × Fin d) T.V) (a : 𝓞 E) (m : ℕ) (ha : xT m ≫ I.G.act.act a =
      Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (actT p.2)) ≫ xT m) :
    xL I xT m ≫ (I.t'.act.act a).left =
      spMap ((jetSubstP m fun p : Fin 1 × Fin d => MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (actT p.2)) :
        Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
          Jet T.Fr (Fin 1 × Fin d) m →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT m := by
  apply ext2 I
  · rw [Category.assoc, I.m2.act a, ← Category.assoc, xL_fst, Category.assoc, Category.assoc, xL_fst,
      ← Category.assoc (spMap _) (spMap _), spMap_comp', ← jetCoef_substP, ← spMap_comp', Category.assoc]
    exact congrArg (spMap (jc (d := d) 1 m) ≫ ·) (congrArg CommaMorphism.left ha)
  · rw [Category.assoc, Over.w (I.t'.act.act a), Category.assoc, xL_snd, spMap_algHom_alg]

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
section
set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem expChartOf_of (hAct : ExpActOfSt) : ExpChartOfSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C
  obtain ⟨φ, hφ⟩ := isExpOf_exists C
  exact ⟨φ, hφ, ExpChartJet.isExpChart_of_expOf C φ hφ (hAct E H Dw l Xo c S y C φ hφ)⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieGerm
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x :=
  ReciprocityTheory.ChartRestriction.G.DVR.res_res' h1 h2 x

private theorem gs_idRes_lemma {X Y : Scheme.{0}} (h : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    (hV : W ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ W) (x : Γ(X, U)) :
    gs (𝟙 Y) y W ((Y.presheaf.map (homOfLE hV).op).hom ((h.app U).hom x)) = gs h y U x := by
  rw [gs_res (𝟙 Y) y hV hy, gs_pull (𝟙 Y) h y U (hV hy), Category.id_comp]

section Corr

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

theorem corr_pullGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (H : LB.Gen.Corr L φ ε φ' ε' t t')
    (h : Z ⟶ Y) : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) (LB.pullGen L φ' ε' t' h) := by
  intro j j' hj hj' hjj
  have hc : LB.Coh L φ j := fun k1 k2 e => hj k1 k2 (congrArg (fun f => h ≫ f) e)
  have hc' : LB.Coh L φ' j' := fun k1 k2 e => hj' k1 k2 (congrArg (fun f => h ≫ f) e)
  have hx : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' e => hjj k k' (congrArg (fun f => h ≫ f) e)
  have E := congrArg Units.val (H j j' hc hc' hx)
  apply Units.ext
  simp only [LB.pullGen, res, pullU, Units.coe_map, MonoidHom.coe_coe] at E ⊢
  apply fn_ext
  intro y hy
  have hy1 : h y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' :=
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  erw [gs_res (𝟙 Z) y _ hy, gs_idRes_lemma h _ y hy.1]
  erw [gs_res (𝟙 Z) y _ hy, gs_idRes_lemma h _ y hy.2]
  erw [← gs_res h y inf_le_left hy1, ← gs_res h y inf_le_right hy1]
  exact congrArg _ E

theorem corr_refl {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen.Corr L φ ε φ ε t t := by
  intro j j' _ _ hjj
  obtain rfl : j = j' := funext fun k => hjj k k rfl
  rfl

end Corr

section Xo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_scale {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Xo.univ.t.G.left)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} {t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')}
    (Hc : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' t t') (w : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (scaleGen φ ε w t) (scaleGen φ' ε' w t') := by
  intro j j' hj hj' hjj
  have e := Hc j j' hj hj' hjj
  have key : ∀ {U V : Y.Opens} (hle : V ≤ U) (a b : Γ(Y, U)ˣ), res hle (a * b) = res hle a * res hle b :=
    fun hle a b => map_mul _ a b
  erw [key, key, res_res', res_res', e]

theorem corr_genPow {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Xo.univ.t.G.left)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} {t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')}
    (Hc : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' t t') (k : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (genPow φ ε t k) (genPow φ' ε' t' k) := by
  intro j j' hj hj' hjj
  have key : ∀ {U V : Y.Opens} (hle : V ≤ U) (a : Γ(Y, U)ˣ), res hle (a ^ k) = res hle a ^ k :=
    fun hle a => map_pow _ a k
  show res _ (t.s j ^ k) = res _ (t'.s j' ^ k)
  erw [key, key]
  exact congrArg (· ^ k) (Hc j j' hj hj' hjj)

theorem genPow_scale_pull {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε))
    (h : Z ⟶ Y) (w : Γ(Z, ⊤)ˣ) (k : ℕ) :
    genPow _ _ (scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L φ ε t h)) k =
      scaleGen _ _ (w ^ k) (LB.pullGen Xo.univ.t.PP.L φ _ (genPow φ ε t k) h) := by
  simp only [genPow, scaleGen, LB.pullGen, mul_pow, map_pow]
  have hp : ∀ {U : Y.Opens} {W : Z.Opens} (hle : W ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)ˣ),
      res hle (pullU h U (x ^ k)) = res hle (pullU h U x) ^ k := fun hle x => by rw [map_pow, map_pow]
  congr 1
  funext j
  congr 1
  exact (hp _ _).symm

end Xo

section Pull

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

set_option maxHeartbeats 1000000 in
theorem isPullSec_comp (a : ℤ) {T1 T2 T3 : Over S0} (h1 : T2 ⟶ T1) (h2 : T3 ⟶ T2)
    {s1 : LB.Sec (LPow A L a T1)} {s2 : LB.Sec (LPow A L a T2)} {s3 : LB.Sec (LPow A L a T3)}
    (e1 : IsPullSec A L a (h1 ▷ A) (whiskerRight_snd _ _) s1 s2)
    (e2 : IsPullSec A L a (h2 ▷ A) (whiskerRight_snd _ _) s2 s3) :
    IsPullSec A L a ((h2 ≫ h1) ▷ A) (whiskerRight_snd _ _) s1 s3 := by
  intro j
  apply fn_ext
  intro y hy
  have hy2 : (h2 ▷ A).left y ∈ (LPow A L a T2).U j :=
    chart_le_res A L (h2 ▷ A) (whiskerRight_snd _ _) a j hy
  rw [GermD.pullSec_stalk (A := A) (L := L) a e2 (𝟙 _) y j hy, Category.id_comp,
    GermD.pullSec_stalk (A := A) (L := L) a e1 (h2 ▷ A).left y j hy2,
    gs_idRes_lemma _ _ y hy, comp_whiskerRight, Over.comp_left]

theorem isPullSec_congr (a : ℤ) {T T' : Over S0} {h h' : T' ⟶ T} (e : h = h')
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (hs : IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) s s') :
    IsPullSec A L a (h' ▷ A) (whiskerRight_snd _ _) s s' := by
  subst e
  exact hs

theorem ptSecT_whisker {T T' : Over S0} (h : T' ⟶ T) (z : T ⟶ A) :
    (ptSecT A (h ≫ z)).left ≫ (h ▷ A).left = h.left ≫ (ptSecT A z).left := by
  have e : ptSecT A (h ≫ z) ≫ (h ▷ A) = h ≫ ptSecT A z := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e2 := congrArg (fun f => f.left) e
  simpa using e2

end Pull

section Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isValueAt_pullScale (hL : Xo.univ.t.PP.L.IsLB) (a : ℤ) {T T' : Over Xo.X} (h : T' ⟶ T)
    {s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L a T)} {s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L a T')}
    (hs : IsPullSec Xo.univ.t.G Xo.univ.t.PP.L a (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) s s')
    {z : T ⟶ Xo.univ.t.G}
    {τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := T.left) (K := Fin 1) (fun _ => z.left) fun _ => a)}
    {v : Γ(T.left, ⊤)} (hv : IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s z τ v) (w : Γ(T'.left, ⊤)ˣ) :
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s' (h ≫ z)
      (scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L _ _ τ h.left))
      ((h.left.appTop).hom v * ((w⁻¹ : Γ(T'.left, ⊤)ˣ) : Γ(T'.left, ⊤))) := by
  intro j
  apply fn_ext
  intro y hy
  have hy2 : h.left y ∈ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hy3 : (ptSecT Xo.univ.t.G z).left (h.left y) ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L a T).U j :=
    val_le Xo.univ.t.G Xo.univ.t.PP.L z j hy2
  have hy1 : (ptSecT Xo.univ.t.G (h ≫ z)).left y ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L a T').U j :=
    val_le Xo.univ.t.G Xo.univ.t.PP.L (h ≫ z) j hy
  have hv' : gs h.left y ⊤ v * gs h.left y _ (τ.s j).val =
      gs (h.left ≫ (ptSecT Xo.univ.t.G z).left) y _ (s.f j) := by
    have e := congrArg (gs h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j)) (hv j)
    rw [gs_mul _ _ _ hy2, gs_res h.left y le_top hy2,
      gs_res h.left y (val_le Xo.univ.t.G Xo.univ.t.PP.L z j) hy2] at e
    exact e.symm.trans (gs_pull h.left (ptSecT Xo.univ.t.G z).left y ((LPow Xo.univ.t.G Xo.univ.t.PP.L a T).U j) hy3
      (s.f j))
  have e1 : gs (𝟙 T'.left) y ⊤ ((h.left.appTop).hom v) = gs h.left y ⊤ v := by
    have := gs_pull (𝟙 T'.left) h.left y ⊤ trivial v
    rw [Category.id_comp] at this
    exact this
  have lhs : gs (𝟙 T'.left) y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j)
      ((T'.left.presheaf.map (homOfLE (val_le Xo.univ.t.G Xo.univ.t.PP.L (h ≫ z) j)).op).hom
        (((ptSecT Xo.univ.t.G (h ≫ z)).left.app _).hom (s'.f j))) =
      gs h.left y ⊤ v * gs h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j) (τ.s j).val := by
    refine (gs_idRes_lemma _ _ y hy _).trans ?_
    refine (GermD.pullSec_stalk (A := Xo.univ.t.G) (L := Xo.univ.t.PP.L) a hs _ y j hy1).trans ?_
    rw [ptSecT_whisker Xo.univ.t.G h z]
    exact hv'.symm
  have pgle : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤
      h.left ⁻¹ᵁ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j :=
    fun _ hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have ex2 : (show Γ(T'.left, LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j) from
          ((scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L _ _ τ h.left)).s j).val) =
      (T'.left.presheaf.map (homOfLE (le_top : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤ ⊤)).op).hom
        w.val *
      (T'.left.presheaf.map (homOfLE pgle).op).hom
        ((h.left.app (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j)).hom (τ.s j).val) := rfl
  have rhs : gs (𝟙 T'.left) y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j)
      ((T'.left.presheaf.map (homOfLE (le_top : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤ ⊤)).op).hom
          ((h.left.appTop).hom v * ((w⁻¹ : Γ(T'.left, ⊤)ˣ) : Γ(T'.left, ⊤))) *
        (show Γ(T'.left, LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j) from
          ((scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L _ _ τ h.left)).s j).val)) =
      gs h.left y ⊤ v * gs h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j) (τ.s j).val := by
    rw [ex2, map_mul, gs_mul (𝟙 _) y _ hy, gs_mul (𝟙 _) y _ hy, gs_mul (𝟙 _) y _ hy,
      gs_res (𝟙 _) y le_top hy, gs_res (𝟙 _) y le_top hy, gs_res (𝟙 _) y pgle hy]
    erw [gs_pull (𝟙 _) h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j) (pgle hy)]
    rw [Category.id_comp, e1]
    erw [gs_res (𝟙 _) y (le_top : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤ ⊤) hy
      (w : Γ(T'.left, ⊤))]
    rw [gs_unit (𝟙 _) y ⊤ trivial w⁻¹, gs_unit (𝟙 _) y ⊤ trivial w, map_inv,
      mul_assoc (gs h.left y ⊤ v), Units.inv_mul_cancel_left]
  exact lhs.trans rhs.symm

end Val

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
end
end

