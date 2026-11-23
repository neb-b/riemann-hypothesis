module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerInvariantLifts
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

noncomputable section

namespace GlobalTheory.InvLiftSymm

theorem exists_symm_invLift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∀ C : Matrix (Fin n) (Fin n) R, (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (C a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) → ∃ Θ : Matrix (Fin n) (Fin n) R, Θᵀ = Θ ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hinv D J V j d hcov hle hlift hwt C hrel
  obtain ⟨g, w, e, P, Qm, he, hPQ, hfac⟩ := _root_.GlobalTheory.InvFactor.exists_basis_pull_matrix R Dd O oa Y n v dd hinv
  have hKS := _root_.GlobalTheory.HeatDescend.ksRel_of_invLifts R Dd O oa Y n v dd hinv g w e P he hfac D J V j d hcov hle hlift hwt C hrel
  have hM : (P * C * Pᵀ)ᵀ = P * C * Pᵀ := _root_.GlobalTheory.KSRelSymm.ksRel_symm R Dd.toPre.P g w e he D _ hKS
  have hM' : P * (Cᵀ * Pᵀ) = P * (C * Pᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at hM
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hM, Matrix.mul_assoc]
  have hQP : Qmᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  set Θ : Matrix (Fin n) (Fin n) R := C * Pᵀ * Qmᵀ + Qm * P * Cᵀ - Qm * (P * C * Pᵀ) * Qmᵀ with hΘ
  have hΘP : Θ * Pᵀ = C * Pᵀ := by
    rw [hΘ, Matrix.sub_mul, Matrix.add_mul]
    simp only [Matrix.mul_assoc, hQP, Matrix.mul_one]
    rw [hM']
    simp only [← Matrix.mul_assoc]
    abel
  refine ⟨Θ, ?_, ?_⟩
  · rw [hΘ]
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hM]
    simp only [Matrix.mul_assoc]
    abel
  · intro i i' W hW f
    rw [hrel i i' W hW f]
    let cf : R →+* Γ(Y.H.left, W) :=
      (Y.H.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    have hcf : ∀ r, constFn Y.H.hom W r = cf r := fun _ => rfl
    have hW' : W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
      fun x hx => ⟨hle i (hW hx).1, hle i' (hW hx).2⟩
    set X : Fin g → Γ(Y.H.left, W) := fun c =>
      pbT Y.q.left (e c _ (Dd.toPre.P.L.g (j i) (j i')).val) W * pbT Y.q.left (Dd.toPre.P.L.g (j i) (j i'))⁻¹.val W
    have hdlg : ∀ b, dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W = ∑ c, cf (P c b) * X c := by
      intro b
      rw [dlg, hfac b _ W hW', Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hcf, _root_.mul_assoc]
    have key : ∀ (A : Matrix (Fin n) (Fin n) R) (a : Fin n),
        ∑ b, cf (A a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W = ∑ c, cf ((A * Pᵀ) a c) * X c := by
      intro A a
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hdlg, Finset.mul_sum, Matrix.mul_apply, Matrix.transpose_apply, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, _root_.mul_assoc]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hcf, ← Finset.sum_mul]
    rw [key Θ a, key C a, hΘP]

end GlobalTheory.InvLiftSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInjBase

theorem val_eq_of_injective {X Y Y₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (e : Y₀ ⟶ Y) (he : Function.Injective e.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ : ∃ a, a = (res le (t.s PEmpty.elim)).val := ⟨_, rfl⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ a := by
    intro Z r z J hJ
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      (congrArg (gs r z ⊤) ha.symm))
  have a1 : a = 1 := he ((fn_ext (V := ⊤) fun y _ => by
    choose I hI using fun χ : Y₀ ⟶ X => exists_chart hM (χ y)
    have := key _ e y I hI
    rw [h y I hI, mul_inv_cancel] at this
    refine (gs_pull (𝟙 Y₀) e y ⊤ trivial a).trans ?_
    rw [Category.id_comp, ← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]).trans (map_one _).symm)
  have := key Z r z J hJ
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem exists_gens {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult)
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ τ : ∀ a b : D.X, LB.Gen (LB.LinComb D.P.L (lamPts (D.c a) (D.c b)) negε), (∀ a b, (τ a b).IsGen) ∧
      (∀ a b z J, Good D.P.L z J → val (τ a b) (𝟙 _) z J = val (τ b a) (𝟙 _) z J) ∧
      (∀ a a' b z J, Good D.P.L z J → val (τ (a + a') b) (𝟙 _) z J * cubV D.cub z J (D.c a) (D.c a') (D.c b) =
        val (τ a b) (𝟙 _) z J * val (τ a' b) (𝟙 _) z J) ∧
      ∀ a b z J, Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ a b) (toUnit (TK R)).left z J := by
  obtain ⟨τ₀, h₀⟩ := GlobalTheory.DDataGens.main R D hB hU
  have cadd : ∀ a b, D.c (a + b) = D.c a * D.c b := D.c_add
  have c0 : D.c 0 = 1 := mul_eq_left.1 ((cadd 0 0).symm.trans (by rw [add_zero]))
  have ex : ∀ a b : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (D.c a) (D.c b)) negε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.P.L z J → val t r z J = val (τ₀ a b) r z J := fun a b =>
    exists_gen D.P.isLB (fun U _ h => by
      simp [lamPts, negε, Fin.prod_univ_four, cadd, c0]) (τ₀ a b) (h₀ a b).1
  choose τ hτ hv using ex
  have hK : ∀ a b z J, Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ a b) (toUnit (TK R)).left z J :=
    fun a b z J hJ => ((h₀ a b).2 z J hJ).trans (hv a b _ _ z J hJ).symm
  have inj : Function.Injective (toUnit (TK R)).left.appTop.hom := by
    rw [GlobalTheory.DDataGens.toUnit_TK_left]
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    intro x y hxy
    refine (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
      (IsFractionRing.injective R (FractionRing R) ?_)
    exact (congrArg (fun g => g.hom x) nat).symm.trans
      ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom hxy).trans (congrArg (fun g => g.hom y) nat))
  refine ⟨τ, hτ, fun a b z J hJ => ?_, fun a a' b z J hJ => ?_, hK⟩
  · refine val_eq_of_injective D.P.isLB (fun U _ h => ?_) _ inj (hτ a b) (hτ b a) (fun y J hJ => ?_) _ _ z J hJ
    · simp only [Fin.prod_univ_four, lamPts, negε, mul_comm (D.c b) (D.c a)]
      simp [mul_right_comm]
    · exact (hK a b y J hJ).symm.trans ((GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a b).trans (hK b a y J hJ))
  · have key := val_eq_of_injective D.P.isLB (fun U _ h => ?_) _ inj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hτ (a + a') b)
        (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (D.c a) (lift (D.c a') (D.c b))).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hτ a b) (hτ a' b)) (fun y J hJ => ?_) _ (𝟙 _) z J hJ
    · refine Eq.trans ?_ (key.trans (val_mul hJ _ _ _))
      refine Eq.trans ?_ (val_mul hJ _ _ _).symm
      refine congrArg (_ * ·) ?_
      have := val_cub D.cub (𝟙 (𝟙_ (Over (Sp R)))) hJ (D.c a) (D.c a') (D.c b)
      simp only [Category.id_comp] at this
      exact this.symm
    · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub (D.c a) (D.c a') (D.c b) h))).trans ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, lamPts, negε, cadd]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv]
      abel
    · refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      rw [← hK _ _ y J hJ, ← hK _ _ y J hJ, ← hK _ _ y J hJ]
      exact (congrArg (_ * ·) (val_cub D.cub (toUnit (TK R)) hJ _ _ _)).trans
        (GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB a a' b)

theorem val_trans {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : LB B.left} (hL : L.IsLB) {T T' : Over S}
    (ρ : T' ⟶ T) (x y : T ⟶ B) {t : LB.Gen (LB.LinComb L (lamPts x y) negε)} (ht : t.IsGen) (z : T'.left) {J J'}
    (hJ : Good L z J) (hJ' : Good L z J') :
    val t ρ.left z J' = lamVal (Wit.idPull (abelian₂ B L)) (lift (ρ ≫ x) (ρ ≫ y)).left z J J' * val t ρ.left z J := by
  refine (gen_trans ht ρ.left z (hJ'.mem _ _) (hJ.mem _ _)).trans (congrArg (· * _) ?_)
  have hm : ∀ {J}, Good L z J → (lift (ρ ≫ x) (ρ ≫ y)).left z ∈ (abelian₂ B L).U
    (fun I => J ((lift (ρ ≫ x) (ρ ≫ y)).left ≫ (psum B (x2 B) I.down).left)) := fun hJ => hJ.mem _ _
  refine Eq.trans ?_ (Wit.gw_idPull (abelian₂ B L) _ z _ _ (hm hJ) (hm hJ')).symm
  refine Eq.trans ?_ (gm_linComb L _ _ _ z _ _ (hm hJ) (hm hJ')).symm
  refine Eq.trans ?_ (GlobalTheory.PrimCocycle.prod_lam (ρ ≫ x) (ρ ≫ y) (fun q => gm q z _ (L.g (J q) (J' q)))).symm
  have inv : ∀ q, gm q z _ (L.g (J' q) (J q)) = (gm q z _ (L.g (J q) (J' q)))⁻¹ := fun q =>
    eq_inv_of_mul_eq_one_left ((gm_cocycle hL q z (hJ' q) (hJ q) (hJ' q)).trans (gm_self hL q z (hJ' q)))
  refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ negε k) (inv (_ ≫ _))).trans ?_
  refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_)
    (Wit.prod_neg_lamPts _ _ (fun q => gm q z _ (L.g (J q) (J' q))))
  have : ρ.left ≫ lamPts x y k = 𝟙 _ ≫ lamPts (ρ ≫ x) (ρ ≫ y) k := by
    rw [Category.id_comp]
    fin_cases k
    · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_mul ρ _ _)
    · rfl
    · rfl
    · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one ρ)
  exact congrArg (fun q => (gm q z _ (L.g (J q) (J' q)))⁻¹ ^ negε k) this

theorem main : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (b : o →+* W) (D : DegPre W), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) → ∀ n : ℕ, ∃ (T : TautBase o W) (ib : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n (mulDeg D n) ib β ββ w := by
  intro o W _ _ _ _ b D hB hU n
  obtain ⟨τ, hg, hs, ha, hK⟩ := exists_gens D hB hU
  obtain ⟨ib⟩ : Nonempty (D.X ≃+ (Fin (Module.finrank ℤ D.X) → ℤ)) := ⟨(Module.finBasis ℤ D.X).equivFun.toAddEquiv⟩
  have hid : spMap (RingHom.id W) = 𝟙 (Sp W) := Spec.map_id _
  have hn : ∀ a : D.X, ib.symm ((n : ℤ) • ib a) = n • a := fun a => by
    rw [map_zsmul, ib.symm_apply_apply, natCast_zsmul]
  let T : TautBase o W :=
    { b := b
      B := D.P.A
      comm := D.P.isAb.comm
      isAb := D.P.isAb
      g := D.P.g
      smoothDim := D.P.smoothDim
      M := ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩
      cub := D.cub
      ample := D.P.ample
      ktriv := D.P.ktriv
      r := Module.finrank ℤ D.X
      c₀ := fun a => D.c (ib.symm a)
      c₀_add := fun a a' => by rw [map_add (f := _)]; exact D.c_add _ _
      τ₀ := fun a a' => τ (ib.symm a) (ib.symm a')
      τ₀_gen := fun a a' => hg _ _
      τ₀_symm := fun a a' => hs _ _
      τ₀_add := fun a a' a'' z J hJ => (congrArg (fun x => val (τ x (ib.symm a'')) (𝟙 _) z J * _) (map_add ib.symm a a')).trans
        (ha _ _ _ z J hJ) }
  refine ⟨T, ib, 𝟙 _, 𝟙 _, Wit.idPull _, ?_, ⟨(Category.id_comp _).trans (Category.comp_id _).symm,
    (Category.id_comp _).trans (Category.comp_id _).symm⟩, Wit.idPull_isGen (DVR.linComb_isLB _ D.P.isLB _ _), fun a => ?_,
    fun (a b : D.X) => ⟨1, by simp, fun z J J' hJ hJ' => ?_⟩⟩
  · rw [hid]
    exact Wit.grpPullback_id D.P.A
  · rw [hid]
    exact (Category.comp_id _).trans ((congrArg (fun x => (D.c x).left) (hn a).symm).trans (Category.id_comp _).symm)
  · have e₁ : val ((mulDeg D n).tau a b) (𝟙 _) z J' = val (D.tau (n • a) (n • b)) (𝟙 _) z J' := by
      refine (GlobalTheory.TauTwist.val_tau (mulDeg D n) a b _ hJ').trans (Eq.trans ?_ (GlobalTheory.TauTwist.val_tau D _ _ _ hJ').symm)
      rw [← nsmul_add]
      rfl
    have e₂ : val (T.τ₀ ((n : ℤ) • ib a) ((n : ℤ) • ib b)) ((TK W).hom ≫ spMap (RingHom.id W)) z J =
        val (τ (n • a) (n • b)) (toUnit (TK W)).left z J := by
      rw [hid, Category.comp_id, GlobalTheory.DDataGens.toUnit_TK_left]
      exact congrArg₂ (fun x y => val (τ x y) (jK W) z J) (hn a) (hn b)
    have e₃ : gm (𝟙 (TK W).left) z ⊤ (unitOn (1 : (FractionRing W)ˣ)) = 1 := (congrArg (gm (𝟙 (TK W).left) z ⊤) (map_one _)).trans (map_one _)
    refine e₁.trans ((hK _ _ z J' hJ').trans (Eq.trans ?_ (congrArg₂ (· * ·) e₃ (congrArg (_ * ·) e₂)).symm))
    rw [_root_.one_mul]
    exact val_trans D.P.isLB (toUnit (TK W)) _ _ (hg (n • a) (n • b)) z hJ hJ'

end GlobalTheory.TInjBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameIsValueAtThetaConstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section
namespace GlobalTheory.Ex.OneGen

open TorsFrame CommPairing

theorem ThG.exists_isTorsFrame_isValueAt : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m : ℕ), Odd m → ∀ (T : Over S) (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (y : T ⟶ P.A) (c : Γ(T.left, ⊤)), GlobalTheory.Ex.OneGen.ThG P.A P.L rig m th y c → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (y ^ m).left) (fun _ => 1)), IsTorsFrame P rig m (y ^ m) τ ∧ IsValueAt P.A P.L ((1 : ℕ) : ℤ) th (y ^ m) (powFrame P.A P.L (y ^ m) τ ((1 : ℕ) : ℤ)) c := by
  intro S _ P rig hr m hm T th y c H
  obtain ⟨hy, t, αT, s₁, θ, hαT, hnT, hs₁, hθ, ht, hc⟩ := H
  have hLaw : Laws := abelianSchemeLaws_all.1
  have hL := P.isLB
  obtain ⟨α₀, h₀⟩ := hLaw.mulPull S P m
  obtain ⟨α, hα, vα⟩ := exists_norm hL hr h₀
  obtain ⟨ν, hν⟩ := exists_gen_negLB hLaw.globalFns S P 1 T
  have e₁ : y.left ≫ (mulA P.A m).left = (y ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have e₂ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, lift_snd, GlobalTheory.TorsFrame.one_left]
  have e₃ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (translPt P.A θ.pt).left = y.left := by
    rw [← Over.comp_left, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, hθ.pt_eq]
    exact congrArg (·.left) (_root_.mul_one y)
  have e₄ : (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]

  obtain ⟨α', hα', vα'⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₄]
      push_cast; rfl)
    (LB.pullGen P.L _ _ α (snd T P.A).left) (DVR.pullGen_isGen _ _ _ _ hα _)

  have eα : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      val αT r z J = val α (r ≫ (snd T P.A).left) z J := by
    intro Z r z J hJ
    refine (gen_unique hL (fst T P.A).left (ptSecT P.A 1).left NormTheta.ptSec_fst
      (CommPairing.surj_fst hLaw.globalFns P.isAb T) hαT hα' (fun w J hJ => ?_) Z r z J hJ).trans
      ((vα' _ _ z J hJ).trans (val_pull hJ _ _ _))
    have a := val_corr hJ hnT (𝟙 _)
    rw [val_pull hJ, Category.id_comp, Ex.OneGen.val_rigT _ _ w hJ, Category.id_comp] at a
    rw [a, vα' _ _ w J hJ, val_pull hJ, show (ptSecT P.A 1).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A from e₂,
      vα _ _ w J hJ, zpow_sub_one, zpow_natCast]
  obtain ⟨τ, hτ, vτ⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (y ^ m).left) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ (GeneratorPullback.powGen P.L _ _
        (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) rig T.hom) (m ^ 2))
      (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _
        (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(m ^ 2 : ℕ), -(m ^ 2 : ℕ)] θ.φ
          (lift (𝟙 T) (1 : T ⟶ P.A)).left) (LB.pullGen P.L _ _ α y.left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _) _)
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
        (DVR.pullGen_isGen _ _ _ _ hα _))))
  have c₀ : ∀ (z : T.left) (J), Good P.L z J → val (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left]
      ![(m ^ 2 : ℕ), -(m ^ 2 : ℕ)] θ.φ (lift (𝟙 T) (1 : T ⟶ P.A)).left) (𝟙 T.left) z J =
        tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J := fun z J hJ =>
    (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)

  have vτ' : ∀ (z : T.left) (J), Good P.L z J → val τ (𝟙 T.left) z J =
      val rig T.hom z J ^ (m ^ 2) * (tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J * val α y.left z J)⁻¹ := by
    intro z J hJ
    rw [vτ _ _ z J hJ, val_mul hJ, val_inv, val_mul hJ, c₀ z J hJ, val_powGen, val_pull hJ, val_pull hJ,
      Category.id_comp, Category.id_comp]
  refine ⟨τ, ⟨by rw [← pow_mul, ← sq, hy], hτ, α, hα, corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩, ThetaCoord.isValueAt_of_sv hL (EvVal.powFrame_isGen P.A P.L _ τ hτ _)
      fun z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · have a : val (powFrame P.A P.L (y ^ m) τ ((m : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ (m ^ 2) :=
      (map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)
    have b := tval_pow hLaw.globalFns P.isAb hL hν hm hα hy hθ hJ
    rw [GlobalTheory.TorsFrame.one_left, vα _ _ z J hJ] at b
    rw [a, vτ' z J hJ, val_mul hJ, val_pull hJ, GlobalTheory.TorsFrame.val_rigT rig _ z hJ, Category.id_comp, Category.id_comp,
      mul_pow, inv_pow, mul_pow, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  ·
    have p₁ : (ptSecT P.A 1).left ≫ (translT P.A θ.pt).left = (lift (𝟙 T) y).left := by
      rw [ptSecT, ThetaCoord.lift_translT, Category.id_comp, hθ.pt_eq, _root_.mul_one]
    have p₂ : (lift (𝟙 T) y).left ≫ (mulT P.A T m).left = (lift (𝟙 T) (y ^ m)).left :=
      ThetaCoord.lift_mulT _ _ _
    have q₁ := VVRank.sv_of_isTwistPull P.A ht (ptSecT P.A 1).left z hJ
    have q₂ := VVRank.sv_of_isTwistPull P.A hs₁ (lift (𝟙 T) y).left z hJ
    rw [p₁, q₂, p₂, hc z J hJ, Ex.OneGen.val_rigT _ _ z hJ, Category.id_comp] at q₁
    rw [eα _ _ z J hJ, show (lift (𝟙 T) y).left ≫ (snd T P.A).left = y.left by rw [← Over.comp_left, lift_snd]] at q₁
    have v₁ : val (powFrame P.A P.L (y ^ m) τ ((1 : ℕ) : ℤ)) (𝟙 T.left) z J = val τ (𝟙 T.left) z J :=
      (map_zpow _ _ _).trans (zpow_one _)
    rw [v₁, vτ' z J hJ]
    rw [zpow_natCast, show val θ.φ (ptSecT P.A 1).left z J = tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J from rfl] at q₁
    have hu := (tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J * val α y.left z J).inv_mul
    rw [Units.val_mul] at hu
    rw [Units.val_mul, ← _root_.mul_assoc, q₁]
    linear_combination (-(VVRank.sv P.A th (lift (𝟙 T) (y ^ m)).left z J)) * hu

end GlobalTheory.Ex.OneGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeMapAtClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.TraitAtClosed

theorem exists_trait_lattice_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsGrpPullback G out.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ T.P.D.toPre.X), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (g' r ^ 2) (h T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm f hf hT x hx R _ _ _ j hR hj G _ _ gm hgm D A U hLB hPsi m hm T ξ hξ hsp
  obtain ⟨hft, hcpl⟩ := _root_.GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar X₁.o₁ X₁.Ω₁ M x hx
  obtain ⟨-, p, hp, hpR⟩ := hcpl R j hj
  haveI := hft
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : CharZero T.V := T.cdvr.2.2
  let f₀ : M.Z.presheaf.stalk x →+* T.V := (M.Z.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ).hom
  have hf₀ : spMap f₀ ≫ M.Z.fromSpecStalk x = ξ := by
    have e : spMap f₀ = Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (M.Z.presheaf.stalkSpecializes hsp) := by
      simp only [f₀, spMap, CommRingCat.ofHom_hom, Spec.map_comp]
    rw [e, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  obtain ⟨V', _, _, _, h, g', hcomp, hinj, hloc, hgj, hirr⟩ :=
    GlobalTheory.TraitLift.exists_lift_of_isCpl (M.Z.presheaf.stalk x) R T.V j hj f₀
  have eq1 : spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ := by
    have e : spMap g' ≫ spMap j = spMap h ≫ spMap f₀ := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hgj]
    rw [← hf₀, ← Category.assoc, e, Category.assoc]
  haveI hch : CharZero V' := charZero_of_injective_ringHom hinj
  have hV' : GlobalTheory.Mum.Base V' := ⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR ⟨inferInstance, hcomp, hch⟩, hch⟩
  obtain ⟨tW, mW, PW, e, he⟩ := _root_.GlobalTheory.UPoinc.TraitPull.exists_pull_unif E H Dw l Xo c T V' hV' inferInstance h hinj hloc
  obtain ⟨βT, hβT, hLT, hactT⟩ := hT T ξ hξ
  have hβ' : IsGrpPullback tW.G out.G (spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x)) (mW.φ ≫ βT) := by
    rw [eq1]; exact mW.cart.comp hβT
  have w : (mW.φ ≫ βT) ≫ out.G.hom = (tW.G.hom ≫ spMap g') ≫ (spMap j ≫ M.Z.fromSpecStalk x) := by
    rw [hβ'.1.w, Category.assoc]
  let β : tW.G.left ⟶ G.left := hgm.1.lift (mW.φ ≫ βT) (tW.G.hom ≫ spMap g') w
  have hβgm : β ≫ gm = mW.φ ≫ βT := hgm.1.lift_fst _ _ _
  have hβG : β ≫ G.hom = tW.G.hom ≫ spMap g' := hgm.1.lift_snd _ _ _
  have hβ : IsGrpPullback tW.G G (spMap g') β := hgm.cancel (by rw [hβgm]; exact hβ') hβG
  have hLBW : LBIso PW.U.LG.L (U.LG.L.pull β) := by
    rw [PW.bundle]
    exact LBIso.trans tW.PP.isLB (pull_isLB out.L.isLB _) (pull_isLB U.LG.isLB _)
      (LBIso.trans tW.PP.isLB (pull_isLB T.t.PP.isLB _) (pull_isLB out.L.isLB _)
        (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mW) (GlobalTheory.LN.GenericPoint.lbIso_pull hLT mW.φ rfl))
      (GlobalTheory.LN.GenericPoint.lbIso_pull hLB β hβgm.symm).symm
  have hGs : IsSemiAbelian G := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ out.G G gm hgm out.semi
  obtain ⟨hker, hU₀ab⟩ := _root_.GlobalTheory.UPoinc.KerAb.ker_mem_and_subset_abLocus E H Dw l Xo c C X₁ M U₀ EE out hAdm T ξ hξ R
    (spMap j ≫ M.Z.fromSpecStalk x) V' h g' hinj eq1
  have hWo : IsOpen ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z)) :=
    U₀.isOpen.preimage (spMap j ≫ M.Z.fromSpecStalk x).continuous
  have hPsiW : ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z)) :=
    fun y jj V hV hVU => hPsi y jj V hV (hVU.trans (Set.preimage_mono hU₀ab))
  obtain ⟨ρ, hρs, hρc, hρe⟩ := _root_.GlobalTheory.Poinc.Eq8.GenRestrict.exists_surjective_coordMap_equivMap R hR G hGs D A U V' hV' inferInstance tW.G tW.semi PW.D PW.A PW.U g' β p hp
    hpR _ hWo hPsiW hker hβ hLBW
  refine ⟨V', inferInstance, inferInstance, inferInstance, h, g', e.toAddEquiv.toAddMonoidHom.comp ρ, hinj, hirr T.ϖ T.irr,
    eq1, e.surjective.comp hρs, ?_, ?_⟩
  · intro y r hr
    obtain ⟨h0, r', hr', hass⟩ := he (ρ y)
    exact ⟨h0, ((hρc y r r' hr hr').pow_pow (n := 2)).trans hass⟩
  · intro a y
    obtain ⟨fR, hfRmon, hfRgm, hfRchar⟩ := hm a
    have hcompat : (tW.act.act a).left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc ((tW.act.act a).left ≫ β) ≫ gm = (tW.act.act a).left ≫ mW.φ ≫ βT := by rw [Category.assoc, hβgm]
          _ = mW.φ ≫ (T.t.act.act a).left ≫ βT := by rw [← Category.assoc, mW.act a, Category.assoc]
          _ = mW.φ ≫ βT ≫ (f a).left := by rw [hactT a]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, hfRgm, reassoc_of% hβgm]
      · rw [Category.assoc, hβG, Category.assoc, Over.w fR, hβG, ← Category.assoc, Over.w (tW.act.act a)]
    have key := hρe fR (tW.act.act a) hfRmon (tW.act.hom a) hcompat (m a) _ hfRchar (_root_.GlobalTheory.UPoinc.endChar_act E H V' hV' tW PW a) y
    show e (ρ (m a y)) = H.bar a • e (ρ y)
    rw [key]
    exact e.map_smul _ _

end GlobalTheory.UPoinc.TraitAtClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalIdealsContainingNatCast
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowDat

theorem finite_maximal_ideals_containing_natCast :
    ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite := by
  intro E _ _ n hn
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  have hI : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hn0
  refine ((Ideal.finite_factors hI).image
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) => v.asIdeal)).subset ?_
  rintro 𝔮 ⟨hmax, hmem⟩
  have hne : 𝔮 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hn0 hmem
  refine ⟨⟨𝔮, hmax.isPrime, hne⟩, ?_, rfl⟩
  show 𝔮 ∣ Ideal.span {(n : 𝓞 E)}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hmem

end GlobalTheory.LowDat
end
end

