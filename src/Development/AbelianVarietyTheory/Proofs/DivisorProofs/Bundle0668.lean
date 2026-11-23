module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSchBc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitDegreeOverPrimeFieldFbar
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnInvSetOfSmoothAlongProdExp
section
open NumberField
open scoped ContDiff

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

theorem prod_ofFn_eq_of_ne {M : Type*} [Monoid M] {k : ℕ} (f : Fin k → M) (i : Fin k)
    (h : ∀ j, j ≠ i → f j = 1) : (List.ofFn f).prod = f i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ih _ i fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem contDiff_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) :
    ContDiff ℝ ∞ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin d) (Fin d) (Cinf E) → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hprod : ∀ (n : ℕ) (g : Fin n → (Fin k → ℝ) → Matrix (Fin d) (Fin d) (Cinf E)),
      (∀ i, ContDiff ℝ ∞ (g i)) → ContDiff ℝ ∞ (fun t => (List.ofFn fun i => g i t).prod) := by
    intro n
    induction n with
    | zero => intro g _; simpa using contDiff_const
    | succ n ih =>
      intro g hg
      simp only [List.ofFn_succ, List.prod_cons]
      exact (hg 0).mul (ih _ fun i => hg _)
  have h := hprod k (fun i t => NormedSpace.exp (t i • X i))
    fun i => hexp.comp ((contDiff_apply ℝ (fun _ => ℝ) i).smul contDiff_const)
  exact T.contDiff.comp (contDiff_const.mul h)

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

theorem hasDerivAt_mulExp (y : Lie E d) (Z : Matrix (Fin d) (Fin d) (Cinf E)) :
    HasDerivAt (fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • Z))) (toL (Matrix.of y * Z)) 0 := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have h := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) Z (0 : ℝ)).const_mul (Matrix.of y))
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem fderiv_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) (i : Fin k) (c : ℝ) :
    fderiv ℝ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) 0 (Pi.single i c) =
      c • toL (Matrix.of y * X i) := by
  set Θ := fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)
  have hΘ : HasFDerivAt Θ (fderiv ℝ Θ 0) (0 : Fin k → ℝ) :=
    ((contDiff_prodExp y X).differentiable (by simp)).differentiableAt.hasFDerivAt
  let J : ℝ →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ) i
  have hJ0 : J 0 = 0 := map_zero J
  have h1 : HasFDerivAt (Θ ∘ J) ((fderiv ℝ Θ 0).comp J) 0 := by
    have hΘ' : HasFDerivAt Θ (fderiv ℝ Θ 0) (J 0) := by rw [hJ0]; exact hΘ
    exact hΘ'.comp (0 : ℝ) J.hasFDerivAt
  have e : Θ ∘ J = fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • X i)) := by
    funext s
    simp only [Function.comp_apply, Θ]
    congr 2
    rw [prod_ofFn_eq_of_ne _ i]
    · simp [J]
    · intro j hj
      simp [J, Pi.single_eq_of_ne hj]
  rw [e] at h1
  have h2 := h1.hasDerivAt.unique (hasDerivAt_mulExp y (X i))
  have h3 : Pi.single i c = c • J 1 := by
    simp [J, ← Pi.single_smul]
  rw [h3, map_smul]
  simpa using congrArg (c • ·) h2

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

theorem contDiffOn_of_prodExp : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (f : GlobalTheory.CuspRep.Lie E d → ℂ)
    (S : Set (Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))), Submodule.span ℝ S = ⊤ →
    (∀ (k : ℕ) (X : Fin k → Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i, X i ∈ S) →
      ∀ y ∈ GlobalTheory.CuspRep.invSet E d, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        f (GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod))) →
    ContDiffOn ℝ ∞ f (GlobalTheory.CuspRep.invSet E d) := by
  intro E _ _ d f S hS hf x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_

  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ S
  haveI : Module.Finite ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := inferInstance
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  set m := Fintype.card b
  let e := Fintype.equivFin b
  let X : Fin m → Matrix (Fin d) (Fin d) (Cinf E) := fun i => (e.symm i).1
  have hXS : ∀ i, X i ∈ S := fun i => hbS (e.symm i).2
  have hXli : LinearIndependent ℝ X := hbli.comp e.symm e.symm.injective
  have hXspan : Submodule.span ℝ (Set.range X) = ⊤ := by
    have : Set.range X = b := by
      ext x; constructor
      · rintro ⟨i, rfl⟩; exact (e.symm i).2
      · intro hx; exact ⟨e ⟨x, hx⟩, by simp [X]⟩
    rw [this, hbspan, hS]
  let B : Module.Basis (Fin m) ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Module.Basis.mk hXli hXspan.ge
  have hdim : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (Lie E d) := by
    rw [Module.finrank_fin_fun]
    exact (Module.finrank_eq_card_basis B).trans (Fintype.card_fin m) |>.symm

  let Lin : (Fin m → ℝ) →ₗ[ℝ] Lie E d :=
    { toFun := fun t => toL (Matrix.of x₀ * ∑ i, t i • X i)
      map_add' := fun s t => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, mul_add]; rfl
      map_smul' := fun c t => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Matrix.mul_smul]; rfl }
  have hLinj : Function.Injective Lin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h1 : Matrix.of x₀ * ∑ i, t i • X i = Matrix.of x₀ * 0 := by
      rw [mul_zero]; exact ht
    have h2 := (show IsUnit (Matrix.of x₀) from hx₀).mul_left_cancel h1
    funext i
    exact Fintype.linearIndependent_iff.1 hXli t h2 i
  let L : (Fin m → ℝ) ≃L[ℝ] Lie E d :=
    (LinearMap.linearEquivOfInjective Lin hLinj hdim).toContinuousLinearEquiv
  set Θ := fun t : Fin m → ℝ =>
      toL (Matrix.of x₀ * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) with hΘdef
  have hΘ : ContDiff ℝ ∞ Θ := contDiff_prodExp x₀ X
  have hΘ0 : Θ 0 = x₀ := by
    simp [Θ]
  have hD : HasFDerivAt Θ (L : (Fin m → ℝ) →L[ℝ] Lie E d) 0 := by
    have h := ((hΘ.differentiable (by simp)) 0).hasFDerivAt
    have hE : ((L : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) =
        ((fderiv ℝ Θ 0 : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) := by
      refine LinearMap.pi_ext fun i c => ?_
      change Lin (Pi.single i c) = fderiv ℝ Θ 0 (Pi.single i c)
      rw [hΘdef, fderiv_prodExp]
      simp only [Lin, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp only [Pi.single_eq_same, Matrix.mul_smul]
      rfl
    rw [ContinuousLinearMap.coe_injective hE]
    exact h
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hΨ := hΘ.contDiffAt.to_localInverse hD hn
  have hinv := (hΘ.contDiffAt.hasStrictFDerivAt' hD hn).eventually_right_inverse
  have hc : ContDiffAt ℝ ∞ (f ∘ Θ ∘ hΘ.contDiffAt.localInverse hD hn) (Θ 0) :=
    (hf m X hXS x₀ hx₀).contDiffAt.comp _ hΨ
  rw [hΘ0] at hc hinv
  refine hc.congr_of_eventuallyEq (hinv.mono fun x hx => ?_)
  simp only [Function.comp_apply]
  exact congrArg f hx.symm

end GlobalTheory.SecondKind
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityBaseChangeAffineCofilteredLimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

private theorem eqv_of_isIso' (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := by
  intro n
  refine ⟨fun x y hxy => ?_, fun x => ⟨pull R (inv f) F n x, ?_⟩⟩
  · have hx := pull_comp R (inv f) f F n x
    have hy := pull_comp R (inv f) f F n y
    rw [IsIso.inv_hom_id, pull_id] at hx hy
    rw [hx, hy, hxy]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem contCone_bc_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S), IsAffine W → ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F hF S I _ _ G c hc hG W r hW
  haveI : IsConnected I := IsCofiltered.isConnected I
  obtain ⟨e, -⟩ := bc_sch_iso S W r
  let P : Over S ⥤ Scheme.{0} := Over.pullback r ⋙ Over.forget W
  have hlim : IsLimit (P.mapCone c) := isLimitOfPreserves P hc
  have haff : ∀ i, IsAffine ((G ⋙ P).obj i) := by
    intro i
    change IsAffine (pullback (G.obj i).hom r)
    haveI := hG i
    exact isAffine_of_isAffineHom (pullback.snd (G.obj i).hom r)
  have h1 : ContCone R F (sch.mapCone (P.mapCone c)) := GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I (G ⋙ P) (P.mapCone c) hlim haff
  let α : (G ⋙ P) ⋙ sch ⟶ G ⋙ bc (sch.map r) :=
    { app := fun i => e.hom.app (G.obj i)
      naturality := fun i j f => e.hom.naturality (G.map f) }
  refine (ContCone.iff_of_eqv R F I _ _ (sch.mapCone (P.mapCone c)) ((bc (sch.map r)).mapCone c) α (e.hom.app c.pt)
    (fun i => e.hom.naturality (c.π.app i)) (fun i => eqv_of_isIso' R F _) (eqv_of_isIso' R F _)).1 h1

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityCofilteredLimitRepresentedAffine
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ≅ E') : Eqv R f.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R f.inv F n, fun x => ?_, fun y => ?_⟩
  · rw [← pull_comp, Iso.inv_hom_id, pull_id]
  · rw [← pull_comp, Iso.hom_inv_id, pull_id]

theorem contCone_of_represented : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  intro R _ F hF I _ _ D c hc hD hpt
  choose Z hZ he using hD
  obtain ⟨Z0, ⟨e0⟩⟩ := hpt
  let e : ∀ i, yoneda.obj (Z i) ≅ D.obj i := fun i => (he i).some

  let G : I ⥤ Scheme.{0} :=
    { obj := Z
      map := fun {i j} f => yoneda.preimage ((e i).hom ≫ D.map f ≫ (e j).inv)
      map_id := fun i => yoneda.map_injective (by simp)
      map_comp := fun {i j k} f g => yoneda.map_injective (by simp) }
  let isoYD : G ⋙ yoneda ≅ D := NatIso.ofComponents e (fun {i j} f => by simp [G])

  let s : Cone G :=
    { pt := Z0
      π :=
        { app := fun i => yoneda.preimage (e0.hom ≫ c.π.app i ≫ (e i).inv)
          naturality := fun i j f => yoneda.map_injective (by simp [G]) } }
  have hs : IsLimit s := by
    apply isLimitOfReflects yoneda
    have h1 : IsLimit ((Cone.postcompose isoYD.inv).obj c) := (IsLimit.postcomposeInvEquiv isoYD c).symm hc
    refine h1.ofIsoLimit (Cone.ext e0.symm (fun i => ?_))
    simp [s]
    rfl
  have h0 : ContCone R F (sch.mapCone s) := GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I G s hs hZ
  let αI : G ⋙ sch ≅ D ⋙ disc := (Functor.associator G yoneda disc).symm ≪≫ Functor.isoWhiskerRight isoYD disc
  let βI : sch.obj Z0 ≅ disc.obj c.pt := disc.mapIso e0
  refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F I (G ⋙ sch) (D ⋙ disc) (sch.mapCone s) (disc.mapCone c) αI.hom βI.hom
    (fun i => ?_) (fun i => eqv_of_iso R F (αI.app i)) (eqv_of_iso R F βI)).mp h0
  simp only [Functor.mapCone_π_app, αI, βI, s, sch, Functor.comp_map]
  simp [isoYD, ← Functor.map_comp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupPeriodClassesSumConst
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem cup_per_sum_const {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {n : ℕ} (p q : Fin n → Λ →+ Hol F.V) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc) (c : GlobalTheory.CatCoh.C1 K.Oc)
    (β : Λ → Λ → Hol F.V)
    (h : (∑ i, GlobalTheory.CatCoh.cup K.Oc (K.perCl (p i)) (K.perCl (q i))) = GlobalTheory.CatCoh.H2.mk K.Oc ℓ)
    (hℓ : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show T''.C from ℓ.1 T T' T'' φ ψ) =
      (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)) :
    ∃ c' : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      GlobalTheory.CatCoh.d1 K.Oc c' T T' T'' φ ψ =
        algebraMap (Hol F.V) (K.Oc.obj T'') (∑ i, p i φ.deg * q i ψ.deg - β φ.deg ψ.deg) := by
  simp only [Charts.perCl, GlobalTheory.CatCoh.cup_mk] at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, GlobalTheory.CatCoh.H2.mk_eq_mk] at h
  obtain ⟨f, hf⟩ := h
  refine ⟨f + c, fun T T' T'' φ ψ ↦ ?_⟩
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ
  have e2 := hℓ T T' T'' φ ψ
  rw [map_add (f := _), Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, e]
  rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Submodule.coe_sum]
  simp only [Finset.sum_apply, GlobalTheory.CatCoh.cupZ_apply, Charts.perZ, Charts.mp_Oc] at e2 ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_sub, map_sum]
  simp only [AlgHom.commutes, map_mul]
  ring

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
section
noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

variable {g : ℕ} [Fact g.Prime]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_dg_mul_eq_self (y : _root_.Formalism.CyclotomicNorms.Fbar g) (q : ℕ) :
    y ^ g ^ (_root_.GlobalTheory.GoodCharsCompare.dg y * q) = y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).1]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_dg_mul {d : ℕ} (hd : 0 < d) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ^ (g ^ d - 1) = 1) : ∃ k, d = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
  have hDpos := _root_.GlobalTheory.GoodCharsCompare.dg_pos y
  have hd' : y ^ g ^ d = y := _root_.GlobalTheory.GoodCharsCompare.pow_g_of hy
  refine ⟨d / _root_.GlobalTheory.GoodCharsCompare.dg y, ?_⟩
  have hr : y ^ g ^ (d % _root_.GlobalTheory.GoodCharsCompare.dg y) = y ^ g ^ 0 := by
    rw [pow_zero, pow_one]
    conv_rhs => rw [← hd', ← Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y), pow_add, pow_mul,
      pow_pow_dg_mul_eq_self]
  have h1 := (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).2 _ (Nat.mod_lt _ hDpos) 0 hDpos hr
  have h2 := Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y)
  rw [h1, add_zero] at h2
  exact h2.symm

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_sub_one_eq_one_of_pow_pow_eq_self {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {n : ℕ}
    (h : y ^ g ^ n = y) : y ^ (g ^ n - 1) = 1 := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow n g (Fact.out : g.Prime).pos), pow_succ] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul y).symm)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.root_pow {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι (ZMod g)} (hM : M.det ≠ 0)
    {p : (ZMod g)[X]} {k : ℕ} (hp : Irreducible p) (hk : M.charpoly = p ^ k) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ∈ _root_.Formalism.CyclotomicNorms.rootsBar M.charpoly) : y ^ (g ^ Fintype.card ι - 1) = 1 := by
  have hint := _root_.GlobalTheory.GoodCharsCompare.isInt y
  have hchar0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, ← coeff_zero_eq_aeval_zero',
      map_eq_zero] at hy
    apply hM
    rw [Matrix.det_eq_sign_charpoly_coeff, hy, mul_zero]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [hk, _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar one_ne_zero, map_one] at hy
    exact one_ne_zero hy
  have hyp : aeval y p = 0 := by
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, hk, map_pow] at hy
    exact (pow_eq_zero_iff hk0).mp hy
  have hdvd : minpoly (ZMod g) y ∣ p := minpoly.dvd _ _ hyp
  have hassoc : Associated (minpoly (ZMod g) y) p :=
    associated_of_dvd_dvd hdvd ((minpoly.irreducible hint).dvd_symm hp hdvd)
  have hdeg : p.natDegree = _root_.GlobalTheory.GoodCharsCompare.dg y :=
    (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)).symm
  have hcard : Fintype.card ι = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
    rw [← Matrix.charpoly_natDegree_eq_dim M, hk, natDegree_pow, hdeg, mul_comm]
  apply pow_pow_sub_one_eq_one_of_pow_pow_eq_self hy0
  rw [hcard]
  exact pow_pow_dg_mul_eq_self y k

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.coeff_zero_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    f.coeff 0 ≠ 0 ↔ (0 : _root_.Formalism.CyclotomicNorms.Fbar g) ∉ _root_.Formalism.CyclotomicNorms.rootsBar f := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots_map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective hf, ← aeval_def,
    ← coeff_zero_eq_aeval_zero', map_eq_zero]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.squarefree_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    Squarefree f ↔ (_root_.Formalism.CyclotomicNorms.rootsBar f).Nodup := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [nodup_roots_iff_of_splits (Polynomial.map_ne_zero hf) (IsAlgClosed.splits _), separable_map,
    PerfectField.separable_iff_squarefree]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.primeToPart_map (β : _root_.Formalism.CyclotomicNorms.Fbar g ≃* _root_.Formalism.CyclotomicNorms.Fbar g) (l : ℕ) (x : _root_.Formalism.CyclotomicNorms.Fbar g) :
    _root_.Formalism.CyclotomicNorms.primeToPart l (β x) = β (_root_.Formalism.CyclotomicNorms.primeToPart l x) := by
  unfold _root_.Formalism.CyclotomicNorms.primeToPart
  rw [MulEquiv.orderOf_eq, map_pow]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.eq_minpoly {φ : (ZMod g)[X]} (hm : φ.Monic)
    (hi : Irreducible φ) {x : _root_.Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ _root_.Formalism.CyclotomicNorms.rootsBar φ) : φ = minpoly (ZMod g) x :=
  minpoly.eq_of_irreducible_of_monic hi
    ((_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hm.ne_zero).mp hx) hm

def Ext (ι : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ →* ℂˣ)
    (ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ) : Prop :=
  ∀ u : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ, ((ι u : ℂˣ) : ℂ) = ω u

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_ext {ι : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ →* ℂˣ}
    (hι : Function.Injective ι) :
    ∃ ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ, Function.Injective ω ∧ _root_.GlobalTheory.GoodCharsCompare.Ext ι ω := by
  classical
  let f : _root_.Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if h : x = 0 then 0 else ((ι (Units.mk0 x h) : ℂˣ) : ℂ)
  have hf0 : ∀ x (hx : x ≠ 0), f x = ((ι (Units.mk0 x hx) : ℂˣ) : ℂ) := fun x hx => dif_neg hx
  have hfz : f 0 = 0 := dif_pos rfl
  let ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ :=
    { toFun := f
      map_zero' := hfz
      map_one' := by
        show f 1 = 1
        rw [hf0 1 one_ne_zero, Units.mk0_one, map_one, Units.val_one]
      map_mul' := by
        intro a b
        show f (a * b) = f a * f b
        by_cases ha : a = 0
        · rw [ha, zero_mul, hfz, zero_mul]
        by_cases hb : b = 0
        · rw [hb, mul_zero, hfz, mul_zero]
        rw [hf0 a ha, hf0 b hb, hf0 (a * b) (mul_ne_zero ha hb), Units.mk0_mul, map_mul,
          Units.val_mul] }
  refine ⟨ω, ?_, ?_⟩
  · intro a b hab
    change f a = f b at hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · exfalso
      rw [ha, hfz, hf0 b hb] at hab
      exact Units.ne_zero _ hab.symm
    · exfalso
      rw [hb, hfz, hf0 a ha] at hab
      exact Units.ne_zero _ hab
    · rw [hf0 a ha, hf0 b hb] at hab
      have := hι (Units.ext hab)
      simpa using congrArg Units.val this
  · intro u
    show _ = f u
    rw [hf0 u u.ne_zero, Units.mk0_val]

end GlobalTheory.GoodCharsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLieExistsAdditiveEvalModPrimePowStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n), cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  first | exact @GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow | exact GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow | (intros; apply GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow <;> assumption)
end

