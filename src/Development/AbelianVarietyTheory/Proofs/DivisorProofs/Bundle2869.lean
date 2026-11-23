module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartFunctionsIsWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.TermWt

theorem isWt_term : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Fin 1 → Q.P.L.ι) (V : Y.H.left.Opens), V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j → IsWt Y α V (rsT (τ.f j) V) := by
  intro R _ _ Q O _ _ _ oa Y k α σ τ hT j V hV
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hV' : V ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U j := hV
  have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ V → ∀ z,
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b V (rsT (τ.f j) V))) =
        gs b z (LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j) (τ.f j) := by
    intro b hb z
    rw [valR, dite_eq_left hb, Iso.hom_inv_id_apply, rsT, dite_eq_left hV']
    refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z V (hb trivial) _).trans ?_)
    rw [Category.id_comp]
    exact gs_res b z hV (hb trivial) _
  have hqq : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg CommaMorphism.left hq
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  obtain ⟨J, hJ, hJj⟩ := exists_good Q.P.L hL z (fun _ : Fin 1 => x.left ≫ Y.q.left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b))
    (fun i => Set.mem_iInter.1 (hV (hV₁ (show z ∈ (⊤ : (Sp S).Opens) from trivial))) i)
  have e₁ : ∀ i, J (x.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := hJj
  have e₂ : ∀ i, J (x'.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := fun i => by rw [hqq]; exact hJj i
  have t₁ := hT (Over.mk (spMap φ)) x z J hJ
  have t₂ := hT (Over.mk (spMap φ)) x' z J hJ
  rw [sval_of τ _ z J j e₁] at t₁
  rw [sval_of τ _ z J j e₂, hq, hc α z J hJ, Units.val_mul] at t₂
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  rw [germ _ hV₂ z, t₂, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, t₁,
    show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c α : S) = (unitOn (c α)).val from rfl,
    gs_unit (𝟙 _) z ⊤ trivial]
  exact _root_.mul_left_comm _ _ _

end GlobalTheory.Heat.TermWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermLocalFunctionIsWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat

theorem isWt_rsT_of_isTerm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y k α σ τ hT j V hVj S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  have hle : Y.q.left ⁻¹ᵁ V ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U fun _ => j :=
    fun z hz => Set.mem_iInter.2 fun _ => hVj hz
  have hql : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    have := congrArg CommaMorphism.left hq
    simpa using this

  have key : ((x'.left.appLE (Y.q.left ⁻¹ᵁ V) ⊤ hV').hom (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) =
      (show Γ((Over.mk (spMap φ)).left, ⊤) from (unitOn (c α)).val) * (x.left.appLE (Y.q.left ⁻¹ᵁ V) ⊤ hV).hom (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
    refine fn_ext fun y _ => ?_
    have hy : x.left y ∈ Y.q.left ⁻¹ᵁ V := hV trivial
    have hy' : x'.left y ∈ Y.q.left ⁻¹ᵁ V := hV' trivial
    obtain ⟨J, hJ, eJ⟩ := exists_good Q.P.L Q.P.isLB y (fun _ : Unit => x.left ≫ Y.q.left) (fun _ => j)
      (fun _ _ _ => rfl) (fun _ => hVj hy)
    have e := hT _ x' y J hJ
    have e0 := hT _ x y J hJ
    rw [hq, hc α y J hJ] at e
    rw [gs_mul (𝟙 _) y ⊤ trivial, gs_unit (𝟙 _) y ⊤ trivial, gs_appLE _ _ ⊤ _ (𝟙 _) y trivial,
      gs_appLE _ _ ⊤ _ (𝟙 _) y trivial, Category.id_comp, Category.id_comp]
    simp only [rsT, dif_pos hle]
    erw [gs_res _ y hle hy, gs_res _ y hle hy']
    have e1 := sval_of τ x'.left y J (fun _ => j) (fun _ => (congrArg J hql).trans (eJ ()))
    have e2 := sval_of τ x.left y J (fun _ => j) (fun _ => eJ ())
    rw [e1] at e
    rw [e2] at e0
    refine e.trans ?_
    refine Eq.trans ?_ (congrArg (fun t => _ * t) e0.symm)
    simp only [Units.val_mul]
    ring
  unfold valR
  rw [dif_pos hV, dif_pos hV', key, map_mul]
  congr 1
  simp [unitOn]

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudProjectionSectionValuesIdentity
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FourierDescent

theorem cst_eq_gs_scal {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Z ⟶ Sp R) (z : Z) (C : R) :
    cst p z C = gs (𝟙 _) z ⊤ (scal p C) := by
  have h := gs_pull (𝟙 Z) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom C)
  rw [Category.id_comp] at h
  exact h.symm

theorem values_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α) (C : R), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval σ' Y.q.left y J = sval σ'' Y.q.left y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval σ Y.q.left y J) → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom C) * sval σ x.left z J := by
  intro R _ _ Q O _ _ _ oa Y k α σ σ' σ'' C hyp T x z J hJ
  classical
  have hL := Q.P.isLB
  have : Smooth Y.q.left := GlobalTheory.RayEv.Ray.smooth_q Y
  have : Surjective Y.q.left := (GlobalTheory.RayEv.Ray.surjective_quasiCompact_q Y).1
  have key : ∀ j : Fin 4 → Q.P.L.ι, σ'.f j =
      σ''.f j + constFn Q.P.A.hom ((LB.LinComb Q.P.L (DegPre.famφB Q α) (DegPre.famε k)).U j) C * σ.f j := by
    intro j
    apply GlobalTheory.EigenDescent.app_injective_of_flat_surjective Y.q.left
    apply fn_ext
    intro y hy
    rw [gs_pull (𝟙 _) Y.q.left y _ hy, gs_pull (𝟙 _) Y.q.left y _ hy, Category.id_comp]
    obtain ⟨J', hJ'⟩ : ∃ J', Good Q.P.L y J' :=
      ⟨fun ψ => (exists_chart hL (ψ y)).choose, fun ψ => (exists_chart hL (ψ y)).choose_spec⟩
    have h := hyp y J' hJ'
    have hm := hJ'.mem (DegPre.famφB Q α) Y.q.left
    rw [gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy]
    erw [sec_trans σ' _ y hy hm, sec_trans σ'' _ y hy hm, sec_trans σ _ y hy hm]
    rw [Over.w Y.q, cst_eq_gs_scal]
    change _ * sval σ' Y.q.left y J' = _ * sval σ'' Y.q.left y J' + _ * (_ * sval σ Y.q.left y J')
    rw [h]
    ring
  have hm := hJ.mem (DegPre.famφB Q α) x.left
  change gs x.left z _ (σ'.f _) = gs x.left z _ (σ''.f _) + _ * gs x.left z _ (σ.f _)
  rw [key]
  erw [gs_add _ _ _ hm, gs_mul _ _ _ hm, gs_constFn _ _ _ _ hm]
  rw [Over.w x, cst_eq_gs_scal]
  rfl

end GlobalTheory.FourierDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudShiftUnitIdentityFractionField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

set_option autoImplicit false

namespace GlobalTheory.ShiftUnit

theorem cv_nsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (g : GtPt D T) {y : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J) (a mu : D.X) (k : ℕ) :
    GlobalTheory.TorusModel.cv g (a + k • mu) y J * cubN (th D y J) k (cP D T a) (cP D T mu) g.b =
      GlobalTheory.TorusModel.cv g a y J * GlobalTheory.TorusModel.cv g mu y J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero, pow_zero]; rfl
  | succ k ih =>
    have e := GlobalTheory.TorusModel.cv_add g hJ (a + k • mu) mu
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, e, pow_succ,
      ← _root_.mul_assoc, ← ih, cubN, mul_right_comm]

theorem cst_mul {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a b : V) :
    cst q z (a * b) = cst q z a * cst q z b := by
  unfold cst; rw [map_mul]; exact gs_mul q z ⊤ trivial _ _

theorem cst_pow {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a : V) (n : ℕ) :
    cst q z (a ^ n) = cst q z a ^ n := by
  induction n with
  | zero => unfold cst; rw [pow_zero, pow_zero, map_one, gs_eq q z ⊤ trivial, map_one, map_one]
  | succ n ih => rw [pow_succ, cst_mul, ih, pow_succ]

end GlobalTheory.ShiftUnit


open GlobalTheory.ShiftUnit in
theorem GlobalTheory.ShiftUnit.shift_unit_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  intro R _ _ Q O _ _ _ oa Y hB k mu α xp A₀ B₀ P₀ ψ₀ e hxp hA hP he u hu hcorr Z g pp yp hg hpp z J hJ
  have e1 := (gen_fe (D := Q) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α).2 u hu hcorr _ pp z J hJ
  rw [uVal, val_famMult _ hJ, hg, TWM.val_powGen, TWM.val_powGen] at e1
  have c1 : pp ≫ fst (TF (FractionRing R)) Q.P.A ≫ cP Q (TF (FractionRing R)) mu = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [← Category.assoc, comp_cP]
  have jr : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
  have hr : val (Z := (Over.mk (g ≫ jK R)).left) Q.rigK g z J = val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J := by
    rw [DegPre.rigK, val_pull hJ, jr]
  rw [c1, hpp, hr] at e1
  have b1 : (Y.Φ (Over.mk (g ≫ jK R)) yp).b = yp ≫ Y.q := Ray.Φ_b Y yp
  have b2 : (Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).b = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [Ray.Φ_b, Category.assoc, hxp]; rfl
  have e2 : val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J *
      cubN (th Q z J) k (cP Q (Over.mk (g ≫ jK R)) α) (cP Q (Over.mk (g ≫ jK R)) mu) (yp ≫ Y.q) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ _ yp).s mu) (𝟙 _) z J ^ k := by
    have := cv_nsmul (Y.Φ _ yp) hJ α mu k
    rw [b1] at this
    exact this
  have e3 : val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J *
      th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 _) z J := by
    have := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ yp (toUnit _ ≫ xp))).2 α z J hJ
    rw [b1, b2] at this
    exact this
  have m1 : (yp * (toUnit (Over.mk (g ≫ jK R)) ≫ xp)) * (toUnit (Over.mk (g ≫ jK R)) ≫ xp⁻¹) = yp := by
    rw [GrpObj.comp_inv, mul_inv_cancel_right]
  have e4 : val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J * val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J * val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J *
      val ((Y.Φ _ yp).s mu) (𝟙 _) z J = 1 := by
    have := he (Over.mk (g ≫ jK R)) (yp * (toUnit _ ≫ xp)) z J hJ
    rw [m1] at this
    exact this
  have e5 : (val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J).val = cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val :=
    hP Z g z J hJ
  have e6 : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (toUnit _ ≫ xp)).s α) (𝟙 _) z J).val =
      cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J).val :=
    hA Z g z J hJ
  have V : val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J * val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J * val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J ^ k *
      val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J ^ k =
      (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹ *
        val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J * val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J ^ k * val ((Y.Φ _ yp).s α) (𝟙 _) z J := by
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul e1
    have a2 := congrArg Additive.ofMul e2
    have a4 := congrArg Additive.ofMul e4
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a1 a2 a4 ⊢
    have a4k := congrArg (k • ·) a4
    simp only [smul_add, smul_zero] at a4k
    linear_combination (norm := abel) a1 + a2 + a4k
  have Vv := congrArg Units.val V
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at Vv
  rw [e5, mul_pow] at Vv
  have e3v := congrArg Units.val e3
  simp only [Units.val_mul] at e3v
  have hθ : Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu)) * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) = 1 := Units.mul_inv _
  suffices FINAL : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J).val *
      ((val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J) ^ k).val =
    cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val by exact FINAL
  rw [cst_mul, cst_pow, Units.val_pow_eq_pow_val]
  have hu0 : IsUnit ((val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k) := (Units.isUnit _).pow k
  apply hu0.mul_right_cancel
  linear_combination cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * Vv + cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val * hθ - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e3v - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * (val ((Y.Φ _ yp).s α) (𝟙 _) z J).val * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e6
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

def VS {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y) (x : Sp Ω ⟶ Y)
    (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k : ℕ) (s : FractionRing Ω) : Prop :=
  ∃ (r : R) (σ : SecM (𝟙 Y) L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) L x g k σ ω ∧
    (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * s

theorem VS.half {R Ω : Type} [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}}
    {L : LB Y} {x : Sp Ω ⟶ Y} {g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)} {k : ℕ} {s : FractionRing Ω}
    (h : VS φ L x g k (2 * s)) : VS φ L x g k s := by
  haveI : CharZero R := algebraRat.charZero R
  obtain ⟨r, σ, ω, hr, hv, he⟩ := h
  refine ⟨2 * r, σ, ω, mul_ne_zero two_ne_zero hr, hv, ?_⟩
  rw [he, map_mul, map_mul, map_ofNat, map_ofNat]
  ring

theorem ringOp_sub {Ω : Type} [CommRing Ω] {n : ℕ} (d₁ d₂ : Ω → Ω) (dd : Fin n → Ω → Ω)
    (Θ₁ Θ₂ : Matrix (Fin n) (Fin n) Ω) (u₁ u₂ : Fin n → Ω) (p₁ p₁' p₂ p₂' : Ω) (k : ℕ) (f : Ω) :
    ringOp d₁ dd Θ₁ u₁ p₁ p₁' k f - ringOp d₂ dd Θ₂ u₂ p₂ p₂' k f =
      ringOp (fun y => d₁ y - d₂ y) dd (Θ₁ - Θ₂) (u₁ - u₂) (p₁ - p₂) (p₁' - p₂') k f := by
  simp only [ringOp, Matrix.sub_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem bracket {Ω : Type} [CommRing Ω] {n : ℕ} (d : Ω → Ω) (dd : Fin n → Ω → Ω)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (hl : ∀ a x y, dd a (x * y) = x * dd a y + y * dd a x)
    (ha : ∀ a x y, dd a (x + y) = dd a x + dd a y)
    (Θ : Matrix (Fin n) (Fin n) Ω) (hΘ : Θᵀ = Θ) (u : Fin n → Ω) (p p' : Ω) (k : ℕ) (b c : Ω) :
    b * (ringOp d dd Θ u p p' (k + k) (b * c) - b * ringOp d dd Θ u p p' k c -
        c * ringOp d dd Θ u p p' k b) -
      c * (ringOp d dd Θ u p p' (k + k) (b * b) - b * ringOp d dd Θ u p p' k b -
        b * ringOp d dd Θ u p p' k b) =
      2 * ((k : Ω) * b * (b * d c - c * d b) - ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b)) := by
  have sym : ∀ a e, Θ e a = Θ a e := fun a e => by
    have := congrFun (congrFun hΘ a) e
    simpa [Matrix.transpose_apply] using this
  have swap : ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = ∑ a, ∑ e, Θ a e * (dd a b * dd e c) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [sym]; ring
  have s2 : ∀ f h : Ω, ∑ a, ∑ e, Θ a e * dd a (dd e (f * h)) =
      f * ∑ a, ∑ e, Θ a e * dd a (dd e h) + h * ∑ a, ∑ e, Θ a e * dd a (dd e f) +
        (∑ a, ∑ e, Θ a e * (dd a f * dd e h) + ∑ a, ∑ e, Θ a e * (dd a h * dd e f)) := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [hl, ha, hl, hl]
    ring
  have s1 : ∀ f h : Ω, ∑ a, u a * dd a (f * h) = f * ∑ a, u a * dd a h + h * ∑ a, u a * dd a f := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hl]
    ring
  have swap' : ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = 0 := by
    rw [swap]; ring
  have t1 : ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b) =
      b * ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - c * ∑ a, ∑ e, Θ a e * (dd a b * dd e b) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  simp only [ringOp]
  rw [s2, s2, s1, s1, t1, hd, hd]
  push_cast
  linear_combination b * swap'

end GlobalTheory.HeatSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueInFrameLinearCombination
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem sval_smul_add_smul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : LB.Sec (LB.LinComb L φ ε)) (a b : Γ(Y, ⊤)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (a • s + b • t) r z J = gs r z ⊤ a * sval s r z J + gs r z ⊤ b * sval t r z J := by
  have hm := hJ.mem φ r
  exact (gs_add r z _ hm _ _).trans (congrArg₂ (· + ·)
    ((gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a)))
    ((gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm b))))

theorem gs_base_fn {R Ω : Type} [CommRing R] [CommRing Ω] {Y Z : Scheme.{0}} (p : Y ⟶ Sp R) (φ : R →+* Ω)
    (x : Sp Ω ⟶ Y) (h : x ≫ p = spMap φ) (r : Z ⟶ Sp Ω) (z : Z) (a : R) :
    gs (r ≫ x) z ⊤ (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) =
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (φ a)) := by
  have e₁ := gs_pull (r ≫ x) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  have e₂ := gs_pull r (spMap φ) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  rw [Category.assoc, h] at e₁
  refine e₁.trans (e₂.symm.trans (congrArg (gs r z ⊤) ?_))
  exact (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem exists_isValue_lin : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (g : GlobalTheory.RayEv.Transport.Frame L (x' ≫ 𝟙 G.left)) (k : ℕ) (σ₁ σ₂ : SecM (𝟙 G.left) L k) (ω₁ ω₂ : Ω) (a b : R), IsValue (𝟙 _) L x' g k σ₁ ω₁ → IsValue (𝟙 _) L x' g k σ₂ ω₂ → ∃ σ : SecM (𝟙 G.left) L k, IsValue (𝟙 _) L x' g k σ (φ a * ω₁ + φ b * ω₂) := by
  intro R _ G L Ω _ φ x' h g k σ₁ σ₂ ω₁ ω₂ a b h₁ h₂
  refine ⟨(show Γ(G.left, ⊤) from G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) • σ₁ +
    (show Γ(G.left, ⊤) from G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b)) • σ₂,
    fun Z r z J hJ => ?_⟩
  refine (sval_smul_add_smul σ₁ σ₂ _ _ (r ≫ x') z hJ).trans ?_
  rw [h₁ Z r z J hJ, h₂ Z r z J hJ, map_add (f := _), map_mul, map_mul, gs_add r z ⊤ trivial, gs_mul r z ⊤ trivial,
    gs_mul r z ⊤ trivial, ← gs_base_fn G.hom φ x' h r z a, ← gs_base_fn G.hom φ x' h r z b, add_mul, _root_.mul_assoc,
    _root_.mul_assoc]

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianIsAbelianSchemeLocalizationAbelianLoc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusAtPrime

theorem isAbelianScheme_localization : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) := by
  intro R _ _ _ G₁ _ _ hG p _ hp
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsDomain (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isDomain_localization p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  set f := spMap (algebraMap R (Localization.AtPrime p.asIdeal)) with hf
  have hG' : IsSemiAbelian ((Over.pullback f).obj G₁) := IsSemiAbelian.pullback f G₁ hG
  have hopen : IsOpen (abLocus G₁) := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G₁ hG
  have hgen : ∀ z : Sp (Localization.AtPrime p.asIdeal), f z ∈ abLocus G₁ := by
    intro z
    have hle : (f z) ⤳ p := by
      refine (PrimeSpectrum.le_iff_specializes (R := R) (f z) p).1 ?_
      have hr : (f z : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))) := by
        exact ⟨z, rfl⟩
      rw [PrimeSpectrum.localization_comap_range (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl] at hr
      show (f z : PrimeSpectrum R).asIdeal ≤ (p : PrimeSpectrum R).asIdeal
      intro x hx
      by_contra hxp
      exact Set.disjoint_left.1 hr hxp hx
    exact hle.mem_open hopen hp
  have hab : abLocus ((Over.pullback f).obj G₁) = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G₁.hom f) z).1 (hgen z)
  exact
    { comm := hG'.comm
      smooth := hG'.smooth
      proper := GlobalTheory.AbLocusProperNormal.isProper_of_abLocus_eq_univ _ _ hG' hab
      geomConnected := hG'.geomConnected }

end GlobalTheory.AbLocusAtPrime
end

