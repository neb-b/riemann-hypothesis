module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.GaugeValues

theorem vF_eq {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (z : Sp F) (t : LB.Gen (LB.LinComb L φ ε))
    (r : Sp F ⟶ Y) : (((TorusExt.stalkUnits z).symm (val t r z J) : Fˣ) : F) = vF t r J := by
  have h : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ φ k)) := fun w _ =>
    Good.mem (L := L) (z := w) (J := J) (fun ψ => hJ ψ trivial) φ r
  refine (TorusExt.stalkConst z).injective ?_
  rw [← TorusExt.stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (gs_unit r z _ (h trivial) _).symm.trans (TorusExt.gs_eq_stalkConst r z h _)

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem val_sym_one {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J) :
    val D.sym (1 : T ⟶ D.P.A).left z J = 1 := by
  have s := val_corr hJ D.sym_rig (toUnit T).left
  rw [val_pull hJ, val_one] at s
  exact s

theorem prod_sym {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i : Fin 2, h (x.left ≫ ![(ι[D.P.A]).left, 𝟙 D.P.A.left] i) ^ (![1, -1] : Fin 2 → ℤ) i =
      h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (x ≫ ι[D.P.A]).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [zpow_one, zpow_neg_one, Category.comp_id]; rfl

theorem val_sym_mul (hG : GlobalFnsSt) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J)
    (x y : T ⟶ D.P.A) :
    val D.sym (x * y).left z J * cubV D.cub z J x x⁻¹ y⁻¹ =
      val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J y y⁻¹ x := by
  let p : D.P.A ⊗ D.P.A ⟶ D.P.A := fst _ _
  let q : D.P.A ⊗ D.P.A ⟶ D.P.A := snd _ _
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (a b : T' ⟶ D.P.A) {z : T'.left} {J}, Good D.P.L z J →
      val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.sym (p * q).left)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift p (lift p⁻¹ q⁻¹)).left)) (lift a b).left z J =
        val D.sym (a * b).left z J * cubV D.cub z J a a⁻¹ b⁻¹ ∧
      val (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.sym p.left)
        (LB.pullGen D.P.L _ _ D.sym q.left))
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift q (lift q⁻¹ p)).left)) (lift a b).left z J =
        val D.sym a.left z J * val D.sym b.left z J * cubV D.cub z J b b⁻¹ a := by
    intro T' a b z J hJ
    have e₁ : lift a b ≫ p = a := lift_fst _ _
    have e₂ : lift a b ≫ q = b := lift_snd _ _
    have e₃ : lift a b ≫ (p * q) = a * b := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂])
    have e₄ : lift a b ≫ p⁻¹ = a⁻¹ := (map_inv (preHom (lift a b)) p).trans (congrArg (·⁻¹) e₁)
    have e₅ : lift a b ≫ q⁻¹ = b⁻¹ := (map_inv (preHom (lift a b)) q).trans (congrArg (·⁻¹) e₂)
    have vs : ∀ w : D.P.A ⊗ D.P.A ⟶ D.P.A, val (LB.pullGen D.P.L _ _ D.sym w.left) (lift a b).left z J =
        val D.sym (lift a b ≫ w).left z J := fun w => val_pull hJ _ _ _
    refine ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (val_cub D.cub _ hJ _ _ _))).trans ?_,
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (vs _)))
        (val_cub D.cub _ hJ _ _ _))).trans ?_⟩
    · rw [e₁, e₃, e₄, e₅]
    · rw [e₁, e₂, e₅]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A ⊗ D.P.A := lift 1 1
  have he : e.left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  refine (ev x y hJ).1.symm.trans (Eq.trans (gen_unique' D.P.isLB (fun V _ k => ?_) _ e.left he
    (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.sym_gen _) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)
      (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (fun w I hI => ?_) _ (lift x y).left z J hJ) (ev x y hJ).2)
  · refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := thK) (U := V) _
      (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym D p k) (prod_sym D q k))
      (prod_cub q q⁻¹ p k)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 2) (K' := thK) (U := V) _
        (prod_sym D (p * q) k) (prod_cub p p⁻¹ q⁻¹ k)).symm)
    rw [mul_inv_cancel, mul_inv_cancel, _root_.one_mul, _root_.one_mul, mul_inv, mul_comm q p, mul_comm q⁻¹ p]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) w I) := isCub_cubV D.cub hI
    refine (ev 1 1 hI).1.trans (Eq.trans ?_ (ev 1 1 hI).2.symm)
    rw [_root_.mul_one, C.face, C.face, val_sym_one D hI, _root_.mul_one, _root_.mul_one]

theorem exists_numOf : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∀ th : H0 D.P.L 1, (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → ∃ (N : NumD F) (ν : NumOf D F N), ν.J = J ∧ ν.th = th := by
  intro hL R _ _ D hE hB F _ _ J hJ th hth
  let z : (TF (R := R) F).left := IsLocalRing.closedPoint F
  have g : Good D.P.L z J := fun ψ => hJ ψ trivial
  let u : ((TF (R := R) F).left.presheaf.stalk z)ˣ ≃* Fˣ := (TorusExt.stalkUnits (F := F) z).symm
  have C : IsCub (cubV D.cub (T := TF (R := R) F) z J) := isCub_cubV D.cub g
  let ρ : ((TF (R := R) F).left.presheaf.stalk z)ˣ := val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A)
    (ε := fun _ => 1) D.rig (TF (R := R) F).hom z J
  let P : D.X → ((TF (R := R) F).left.presheaf.stalk z)ˣ := fun χ =>
    val (Z := (TF (R := R) F).left) (D.psi χ) (jFK (R := R) F) z J
  obtain ⟨b, e⟩ := TauValues.main R D F
  let N : NumD F :=
    { A := TF (R := R) F ⟶ D.P.A
      θ := fun x y w => u (cubV D.cub z J x y w)
      cub := ⟨fun x y => (congrArg u (C.face x y)).trans (map_one u), fun x y w => congrArg u (C.s01 x y w),
        fun x y w => congrArg u (C.s12 x y w), fun x x' x'' y =>
          (map_mul u _ _).symm.trans ((congrArg u (C.coc x x' x'' y)).trans (map_mul u _ _))⟩
      σ := fun x => u (val D.sym x.left z J)
      σ_one := (congrArg u (val_sym_one D g)).trans (map_one u)
      σ_mul := fun x y => by
        simpa only [map_mul] using congrArg u (val_sym_mul D hL.globalFns g x y)
      th := fun x => sF th x.left J * ((u ρ)⁻¹ : Fˣ)
      X := D.X
      c := DegPre.cF D F
      c_add := fun a a' => (congrArg (toUnit _ ≫ ·) (D.c_add a a')).trans (MonObj.comp_mul _ _ _)
      ψ := fun χ => u (P χ * ρ)
      even := fun χ => by
        have h : P (-χ) * val D.sym (DegPre.cF D F χ).left z J = P χ := e.2 hE z J g χ
        rw [← map_mul, mul_right_comm, h]
      bimult := fun a a' m => by
        have h : P (a + a' + m) * P a * P a' * P m * ρ *
            cubV D.cub z J (DegPre.cF D F a) (DegPre.cF D F a') (DegPre.cF D F m) =
            P (a + a') * P (a + m) * P (a' + m) := b.2 hB z J g a a' m
        simp only [← map_div, ← map_mul]
        refine congrArg u (Additive.ofMul.injective ?_)
        have h' := congrArg Additive.ofMul h
        simp only [ofMul_mul, ofMul_div] at h' ⊢
        linear_combination (norm := abel) h' }
  have hρ : ((u ρ : Fˣ) : F) = vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
      (TF (R := R) F).hom J := vF_eq hJ z _ _
  exact ⟨N,
    { J := J, good := hJ, th := th, th_gen := hth, eA := MulEquiv.refl _, eX := AddEquiv.refl _
      c_eq := fun _ => rfl
      θ_eq := fun _ _ _ => vF_eq hJ z _ _
      σ_eq := fun _ => vF_eq hJ z _ _
      th_eq := fun x => (congrArg (N.th x * ·) hρ.symm).trans (Units.inv_mul_cancel_right _ _)
      ψ_eq := fun χ => (congrArg Units.val (map_mul u _ _)).trans ((Units.val_mul _ _).trans
        (congrArg₂ (· * ·) (vF_eq hJ z _ _) hρ)) }, rfl, rfl⟩

end GlobalTheory.GaugeValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointIndependenceSpreadToGeometricFibres
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

theorem map_linComb_pts {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S}
    {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G')) (a : Fin n → ℕ) :
    ρ (linComb x a) = linComb (fun i => ρ (x i)) a := by
  unfold linComb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact map_pow ρ _ _

theorem linComb_left_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T' : Over S'} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (baseOver S ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = (T'.hom ≫ f) ≫ (x i).left) (a : Fin n → ℕ) :
    (linComb x' a).left ≫ φ = (T'.hom ≫ f) ≫ (linComb x a).left := by
  let U : Over.mk (T'.hom ≫ f) ⟶ baseOver S := Over.homMk (T'.hom ≫ f) (Category.comp_id _)
  have hx' : ∀ i, pushPt h.1.w (x' i) = U ≫ x i := fun i => Over.OverMorphism.ext (hx i)
  have e : pushPt h.1.w (linComb x' a) = U ≫ linComb x a :=
    (map_linComb_pts (pushHom h T') x' a).trans ((congrArg (fun z => linComb z a) (funext hx')).trans
      (map_linComb_pts (preHom U) x a).symm)
  exact congrArg (fun z => z.left) e

theorem exists_forall_sections_ne {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [IsSeparated G.hom]
    {z z' : baseOver (Sp R) ⟶ G} (hz : z ≠ z') :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X : Scheme.{0}) [Nonempty X] (s : X ⟶ Sp R'), (s ≫ spMap g) ≫ z.left ≠ (s ≫ spMap g) ≫ z'.left := by
  let j : (equalizer z z').left ⟶ Sp R := (equalizer.ι z z').left
  have hj : IsClosedImmersion j := isClosedImmersion_equalizer_ι_left z z'
  have hC : IsClosed (Set.range j) := j.isClosedEmbedding.isClosed_range
  have hg : genericPoint (Sp R) ∉ Set.range j := by
    intro hg
    have hd : IsDominant j := by
      refine ⟨?_⟩
      rw [DenseRange, dense_iff_closure_eq, hC.closure_eq]
      exact Set.eq_univ_of_univ_subset (((genericPoint_spec (Sp R)).mem_closed_set_iff hC).1 hg)
    refine hz (Over.OverMorphism.ext ?_)
    have hr : IsReduced (baseOver (Sp R)).left := inferInstanceAs (IsReduced (Sp R))
    refine ext_of_isDominant_of_isSeparated G.hom ((Over.w z).trans (Over.w z').symm) j ?_
    exact congrArg (fun u => u.left) (equalizer.condition z z')
  obtain ⟨a, ha, H⟩ := exists_forall_mem (V := ⟨(Set.range j)ᶜ, hC.isOpen_compl⟩) hg
  refine ⟨a, ha, fun R' _ g hga X hX s e => ?_⟩
  obtain ⟨x⟩ := hX
  let U : Over.mk (s ≫ spMap g) ⟶ baseOver (Sp R) := Over.homMk (s ≫ spMap g) (Category.comp_id _)
  have hU : U ≫ z = U ≫ z' := Over.OverMorphism.ext e
  have hl : (equalizer.lift U hU).left ≫ j = s ≫ spMap g := congrArg (fun u => u.left) (equalizer.lift_ι U hU)
  refine H R' g hga (s x) ⟨(equalizer.lift U hU).left x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl]
  rfl

theorem exists_forall_linComb_injective : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSeparated G.hom → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (n k : ℕ) (y : Fin n → (baseOver (Sp R) ⟶ G)) (y₀ : Fin n → (baseOver (Sp K) ⟶ A)), (∀ i, (y₀ i).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ c c' : Fin n → Fin k, linComb y₀ (fun i => (c i : ℕ)) = linComb y₀ (fun i => (c' i : ℕ)) → c = c') → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left) (y' : Fin n → (baseOver (Sp R') ⟶ G')), IsGrpPullback G' G (spMap g) π → (∀ i, (y' i).left ≫ π = spMap g ≫ (y i).left) → ∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R') (c c' : Fin n → Fin k), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c' i : ℕ)) → c = c' := by
  intro R K _ _ _ _ _ _ G _ A _ φ hsep hA n k y y₀ hy hind
  have key : ∀ p : (Fin n → Fin k) × (Fin n → Fin k), ∃ a : R, a ≠ 0 ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
        ∀ (X : Scheme.{0}) [Nonempty X] (s : X ⟶ Sp R'),
          (s ≫ spMap g) ≫ (linComb y (fun i => (p.1 i : ℕ))).left =
            (s ≫ spMap g) ≫ (linComb y (fun i => (p.2 i : ℕ))).left → p.1 = p.2 := by
    rintro ⟨c, c'⟩
    by_cases hc : c = c'
    · exact ⟨1, one_ne_zero, fun _ _ _ _ _ _ _ _ => hc⟩
    have hne : linComb y (fun i => (c i : ℕ)) ≠ linComb y (fun i => (c' i : ℕ)) := by
      intro e
      refine hc (hind c c' (Over.OverMorphism.ext (hA.1.hom_ext ?_ ?_)))
      · have hy' : ∀ i, (y₀ i).left ≫ φ =
            ((baseOver (Sp K)).hom ≫ spMap (algebraMap R K)) ≫ (y i).left := fun i =>
          (hy i).trans (congrArg (· ≫ (y i).left) (Category.id_comp _).symm)
        rw [linComb_left_push hA y₀ y hy', linComb_left_push hA y₀ y hy', e]
      · exact (Over.w _).trans (Over.w _).symm
    obtain ⟨a, ha, H⟩ := exists_forall_sections_ne hne
    exact ⟨a, ha, fun R' _ g hg X _ s e => (H R' g hg X s e).elim⟩
  choose a ha H using key
  refine ⟨∏ p, a p, Finset.prod_ne_zero_iff.2 fun p _ => ha p, ?_⟩
  intro R' _ g hg G' _ π y' hπ hy' F _ _ s c c' e
  have hu : IsUnit (g (a (c, c'))) :=
    isUnit_of_dvd_unit (map_dvd g (Finset.dvd_prod_of_mem a (Finset.mem_univ _))) hg
  refine H (c, c') R' g hu _ s ?_
  have hx : ∀ i, ((Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i).left ≫ π =
      ((Over.mk s).hom ≫ spMap g) ≫ (y i).left := fun i => by
    show (s ≫ (y' i).left) ≫ π = (s ≫ spMap g) ≫ (y i).left
    rw [Category.assoc, hy' i, Category.assoc]
  have e₁ := linComb_left_push hπ _ y hx (fun i => (c i : ℕ))
  have e₂ := linComb_left_push hπ _ y hx (fun i => (c' i : ℕ))
  rw [e] at e₁
  exact e₁.symm.trans e₂

end GlobalTheory.GenSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGeneric
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenSpread

theorem isIso_stalkMap_of_flat {X Y : Scheme.{0}} (φ : X ⟶ Y) [Flat φ] [SurjectiveOnStalks φ] (x : X) :
    IsIso (φ.stalkMap x) := by
  have h1 := Flat.stalkMap φ x
  have h2 := φ.stalkMap_surjective x
  algebraize [(φ.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (φ x))
    (B := X.presheaf.stalk x)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x), h2⟩

theorem mem_smoothLocus_of_isPullback {X X₀ S S₀ : Scheme.{0}} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀}
    {φ : X₀ ⟶ X} {j : S₀ ⟶ S} (h : IsPullback φ f₀ f j) [LocallyOfFinitePresentation f] [Flat j]
    [SurjectiveOnStalks j] [Smooth f₀] (x : X₀) : φ x ∈ f.smoothLocus := by
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  have : SurjectiveOnStalks φ :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) h.flip inferInstance
  have := isIso_stalkMap_of_flat φ x
  have := isIso_stalkMap_of_flat j (f₀ x)
  have h0 : (f₀.stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (f₀.smoothLocus_eq_top.ge (Set.mem_univ x))
  have h1 : ((f₀ ≫ j).stalkMap x).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).2 h0
  rw [← h.w, Scheme.Hom.stalkMap_comp] at h1
  exact Scheme.Hom.mem_smoothLocus.mpr
    ((RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).1 h1)

theorem exists_opens_smoothOfRelativeDimension_of_isPullback {X X₀ S S₀ : Scheme.{0}} {f : X ⟶ S}
    {f₀ : X₀ ⟶ S₀} {φ : X₀ ⟶ X} {j : S₀ ⟶ S} (h : IsPullback φ f₀ f j)
    [LocallyOfFinitePresentation f] [Flat j] [SurjectiveOnStalks j] (n : ℕ)
    [SmoothOfRelativeDimension n f₀] (x : X₀) :
    ∃ W : X.Opens, φ x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f) := by
  have : Smooth f₀ := SmoothOfRelativeDimension.smooth n _
  have hz := mem_smoothLocus_of_isPullback h x
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have h1 : SmoothOfRelativeDimension (0 + n) (pullback.snd f j) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  have h2 : SmoothOfRelativeDimension (0 + (0 + (0 + n))) (pullback.snd (f.smoothLocus.ι ≫ f) j) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨W, hW, hW'⟩ := GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension
    (f.smoothLocus.ι ≫ f) j n (by simpa using h2) ⟨φ x, hz⟩ (f₀ x) (by
      change f (φ x) = _
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w])
  let i := W.ι ≫ f.smoothLocus.ι
  refine ⟨i.opensRange, ⟨⟨⟨φ x, hz⟩, hW⟩, rfl⟩, ?_⟩
  have e : i.opensRange.ι ≫ f = i.isoOpensRange.inv ≫ (W.ι ≫ f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  have h3 : SmoothOfRelativeDimension (0 + n)
      (i.isoOpensRange.inv ≫ (W.ι ≫ f.smoothLocus.ι ≫ f)) := inferInstance
  rw [e]
  simpa using h3

theorem exists_smoothOfRelativeDimension :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → IsProper f → SmoothOfRelativeDimension n f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → SmoothOfRelativeDimension n f' := by
  intro R K _ _ _ _ _ _ n X X₀ f f₀ φ h hf hf₀
  have : LocallyOfFinitePresentation f := inferInstance
  have : Flat (spMap (algebraMap R K)) := flat_specMap_localization (nonZeroDivisors R) K
  have : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  let U : X.Opens := ⨆ W : {W : X.Opens // SmoothOfRelativeDimension n (W.ι ≫ f)}, W.1
  have hc : IsClosed (f '' (U : Set X)ᶜ) := f.isClosedMap _ U.2.isClosed_compl
  obtain ⟨a, ha, H⟩ := exists_forall_notMem (K := K) hc (by
    rintro w ⟨z, hz, e⟩
    obtain ⟨x, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h z w e
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_isPullback h n x
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩))
  refine ⟨a, ha, fun R' _ g hg X' π f' hp => ?_⟩
  have h1 : SmoothOfRelativeDimension n (pullback.snd f (spMap g)) := by
    refine GlobalTheory.ProperFlatNearFibre.smoothOfRelativeDimension_pullback_snd _ _ n fun z y e => ?_
    have h2 : z ∈ U := by
      by_contra hz
      exact H R' g hg y ⟨z, hz, e⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩
  have h2 : SmoothOfRelativeDimension (0 + n) (hp.isoPullback.hom ≫ pullback.snd f (spMap g)) :=
    inferInstance
  simpa using h2

end GlobalTheory.GenSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymSpread

variable {S U : Scheme.{0}} {G : Over S} {A : Over U} [GrpObj G] [GrpObj A] {j : U ⟶ S} {a : A.left ⟶ G.left}

theorem isPullback_square (h : IsGrpPullback A G j a) :
    IsPullback (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left (A ⊗ A).hom (G ⊗ G).hom j := by
  let l := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have l₁ : l.left ≫ pullback.fst G.hom G.hom = pullback.fst A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have l₂ : l.left ≫ pullback.snd G.hom G.hom = pullback.snd A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have big : IsPullback (pullback.snd A.hom A.hom ≫ a) (pullback.fst A.hom A.hom) G.hom (A.hom ≫ j) :=
    (IsPullback.of_hasPullback A.hom A.hom).flip.paste_horiz h.1
  have h₁ : IsPullback l.left (pullback.fst A.hom A.hom) (pullback.fst G.hom G.hom) a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd G.hom G.hom) (v₁₃ := G.hom) (h₂₂ := G.hom) ?_
      l₁ (IsPullback.of_hasPullback G.hom G.hom).flip
    rw [l₂, h.1.w]
    exact big
  exact h₁.paste_vert h.1

theorem pushPt_comp (h : IsGrpPullback A G j a) {u' : A ⟶ A} {u : G ⟶ G} (e : a ≫ u.left = u'.left ≫ a)
    {T : Over U} (x : T ⟶ A) : pushPt h.1.w (x ≫ u') = pushPt h.1.w x ≫ u :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ← e, Category.assoc])

variable [IsCommMonObj G] [IsCommMonObj A]

theorem lbIso_cube (h : IsGrpPullback A G j a) {L : LB G.left} {LA : LB A.left} (hL : L.IsLB) (hLA : LA.IsLB)
    (hb : LBIso LA (L.pull a)) {T : Over S} {T' : Over U} {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ A))
    (V : Over.mk (T'.hom ≫ j) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = V ≫ x i) :
    LBIso (cubeLB A x' LA) ((cubeLB G x L).pull V.left) :=
  LBIso.trans (DVR.linComb_isLB _ hLA _ _) (DVR.linComb_isLB _ (LB.isLB_pull hL a) _ _)
    (LB.isLB_pull (DVR.linComb_isLB _ hL _ _) _) (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.chartPull (chartPullLinComb L a _ _ _ V.left fun I => psum_push h _ _ V hx I.down)
      (Geo.Tor.chartPullPull _ V.left V.left rfl) (lbIso_refl (DVR.linComb_isLB _ hL _ _)))

theorem lbIso_sym (h : IsGrpPullback A G j a) {L : LB G.left} {LA : LB A.left} (hL : L.IsLB) (hLA : LA.IsLB)
    (hb : LBIso LA (L.pull a)) {w wd : G ⟶ G} {w' wd' : A ⟶ A}
    (pa : ∀ {T : Over U} (x : T ⟶ A), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w)
    (pd : ∀ {T : Over U} (x : T ⟶ A), pushPt h.1.w (x ≫ wd') = pushPt h.1.w x ≫ wd) :
    LBIso (cubeLB A ![𝟙 A, w'] LA) ((cubeLB G ![𝟙 G, w] L).pull a) ∧
    LBIso (cubeLB A ![fst A A ≫ w', snd A A] LA) ((cubeLB G ![fst G G ≫ w, snd G G] L).pull
      (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left) ∧
    LBIso (cubeLB A ![fst A A, snd A A ≫ wd'] LA) ((cubeLB G ![fst G G, snd G G ≫ wd] L).pull
      (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left) := by
  refine ⟨?_, lbIso_cube h hL hLA hb _ _ _ fun i => ?_, lbIso_cube h hL hLA hb _ _ _ fun i => ?_⟩
  · let V := pushPt h.1.w (𝟙 A)
    have hV : V.left = a := Category.id_comp _
    have c := lbIso_cube h hL hLA hb ![𝟙 G, w] ![𝟙 A, w'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rwa [hV] at c
  · fin_cases i
    · exact (pa _).trans (by simp)
    · simp
  · fin_cases i
    · simp
    · exact (pd _).trans (by simp)

theorem exists_forall_hypS : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → ∀ (w wd : G ⟶ G) (w₀ wd₀ : A ⟶ A), φ ≫ w.left = w₀.left ≫ φ → φ ≫ wd.left = wd₀.left ≫ φ → IsMonHom w₀ → IsMonHom wd₀ → w₀ * wd₀ = 𝟙 A → LBIso L₀ (cubeLB A ![𝟙 A, w₀] L₀) → LBIso (cubeLB A ![fst A A ≫ w₀, snd A A] L₀) (cubeLB A ![fst A A, snd A A ≫ wd₀] L₀) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → HypS G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ hb w wd w₀ wd₀ ew ewd hw₀ hwd₀ hs hp ha
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap R K)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG.proper
  have hw : IsMonHom w := ExtUnique.isMonHom_of_isGrpPullback h h w₀ w ew.symm
  have hwd : IsMonHom wd := ExtUnique.isMonHom_of_isGrpPullback h h wd₀ wd ewd.symm
  have hsum : w * wd = 𝟙 G := by
    refine ExtUnique.over_hom_ext_of_isPullback h.1 ?_
    have b : pushPt h.1.w (w₀ * wd₀) = pushPt h.1.w w₀ * pushPt h.1.w wd₀ := map_mul (pushHom h A) _ _
    have c := pushPt_comp h ew (𝟙 A)
    have d := pushPt_comp h ewd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [c, d, ← MonObj.comp_mul, hs] at b
    have e : 𝟙 A.left ≫ φ = (𝟙 A.left ≫ φ) ≫ (w * wd).left := congrArg (fun z => z.left) b
    simp only [Category.id_comp] at e
    simpa using e.symm
  have cl : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x L).IsLB := fun x => DVR.linComb_isLB _ hL _ _
  have cl₀ : ∀ {T : Over (Sp K)} (x : Fin 2 → (T ⟶ A)), (cubeLB A x L₀).IsLB := fun x => DVR.linComb_isLB _ hL₀ _ _
  obtain ⟨c₁, c₂, c₃⟩ := lbIso_sym h hL hL₀ hb (fun x => pushPt_comp h ew x) (fun x => pushPt_comp h ewd x)
  have : IsProper (G ⊗ G).hom := by
    change IsProper (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  obtain ⟨a₁, ha₁, H₁⟩ := GenSpread.exists_lbIso G.hom h.1 hL (cl _)
    (hb.symm.trans (LB.isLB_pull hL _) hL₀ (LB.isLB_pull (cl _) _) (hp.trans hL₀ (cl₀ _) (LB.isLB_pull (cl _) _) c₁))
  obtain ⟨a₂, ha₂, H₂⟩ := GenSpread.exists_lbIso (G ⊗ G).hom (isPullback_square h) (cl _) (cl _)
    (c₂.symm.trans (LB.isLB_pull (cl _) _) (cl₀ _) (LB.isLB_pull (cl _) _)
      (ha.trans (cl₀ _) (cl₀ _) (LB.isLB_pull (cl _) _) c₃))
  refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, fun R' _ g hg G' _ _ π L' h' hL' hb' => ?_⟩
  rw [map_mul, IsUnit.mul_iff] at hg
  obtain ⟨w', hw', pa⟩ := SymBaseChange.exists_endo h' w
  obtain ⟨wd', hwd', pd⟩ := SymBaseChange.exists_endo h' wd
  have cl' : ∀ {T : Over (Sp R')} (x : Fin 2 → (T ⟶ G')), (cubeLB G' x L').IsLB := fun x =>
    DVR.linComb_isLB _ hL' _ _
  obtain ⟨d₁, d₂, d₃⟩ := lbIso_sym h' hL hL' hb' pa pd
  refine ⟨w', wd', hw', hwd', ?_, ?_, ?_⟩
  · apply SymBaseChange.pushPt_injective h'
    have b : pushPt h'.1.w (w' * wd') = pushPt h'.1.w w' * pushPt h'.1.w wd' := map_mul (pushHom h' G') _ _
    have c := pa (𝟙 G')
    have d := pd (𝟙 G')
    rw [Category.id_comp] at c d
    rw [b, c, d, ← MonObj.comp_mul, hsum, Category.comp_id]
  · exact hb'.trans hL' (LB.isLB_pull hL _) (cl' _)
      ((H₁ R' g hg.1 _ π G'.hom h'.1.w).trans (LB.isLB_pull hL _) (LB.isLB_pull (cl _) _) (cl' _) d₁.symm)
  · exact d₂.trans (cl' _) (LB.isLB_pull (cl _) _) (cl' _)
      ((H₂ R' g hg.2 _ _ (G' ⊗ G').hom (isPullback_square h').w).trans (LB.isLB_pull (cl _) _) (LB.isLB_pull (cl _) _)
        (cl' _) d₃.symm)

end GlobalTheory.SymSpread
end
end

