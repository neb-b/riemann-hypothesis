module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
section
noncomputable section

namespace GlobalTheory.DvrDeg

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull
attribute [local instance] Over.cartesianMonoidalCategory

section General

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_psiOn_generic (D : DegPre R) [IsOpenImmersion (jK R)] : Nonempty (PsiOn D (jK R).opensRange) := by
  let W := (jK R).opensRange
  let s : W.toScheme ⟶ (TK R).left := (jK R).isoOpensRange.inv
  have hs : s ≫ jK R = W.ι := (jK R).isoOpensRange_inv_comp
  have hr : (jK R ∣_ W) ≫ s = (jK R ⁻¹ᵁ W).ι := by
    rw [← cancel_mono (jK R), Category.assoc, hs, morphismRestrict_ι]
  have hx : ∀ χ, s ≫ D.xK χ = (toUnit (TW W) ≫ D.c χ).left := fun χ => by
    show s ≫ jK R ≫ (D.c χ).left = W.ι ≫ (D.c χ).left
    rw [← Category.assoc, hs]
  choose t ht vt using fun χ => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W) ≫ D.c χ).left) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx χ))
    (LB.pullGen D.P.L _ _ (D.psi χ) s) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) s)
  refine ⟨⟨t, ht, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  refine (val_pull hJ _ _ _).trans ((vt χ _ _ y J hJ).trans ((val_pull hJ _ _ _).trans
    (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
  exact congrArg (fun q => val (D.psi χ) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hr))

theorem exists_isPullDeg_of_val {i : R →+* R'} (hi : Function.Injective i) (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (s : (TK R).left ⟶ W.toScheme) (hs : s ≫ W.ι = jK R)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap hi) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, sq⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = genMap hi ≫ jK R :=
    ⟨genMap hi ≫ s, (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs)⟩
  have hg : g ≫ W.ι = jK R' ≫ specOf i := sq.trans ((fracMap_sq hi).symm.trans (Category.id_comp _))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R').left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = genMap hi ∧
      lam ≫ (jK R ∣_ W) = g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ sq,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))


attribute [local instance] TorusExt.gtGroup in
theorem exists_qkExt_of_inverse {D : DegPre R} {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R) F'] (f : F →+* F') (σ : F' →+* F) (h : f.comp σ = RingHom.id F')
    (hσ : σ.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F) {k : ℕ} (q : QkPt D F' k) :
    ∃ p : QkPt D F k, QkExt f p q := by
  obtain ⟨g, h₁, h₂⟩ := q.eq
  obtain ⟨hb, hv⟩ := (isIota_iff _ _).1 h₂
  have e₁ : GtPtF.IsNsmul k (TorusExt.gtExt D σ hσ q.g) (TorusExt.gtExt D σ hσ g) := by
    rw [TorusExt.isNsmul_iff_eq] at h₁ ⊢
    rw [h₁, map_nsmul]
  have e₂ : GtPtF.IsIota q.y (TorusExt.gtExt D σ hσ g) :=
    (isIota_iff _ _).2 ⟨by rw [TorusExt.gtExt_b, hb, DVR.comp_cP], fun χ y J hJ =>
      (TorusExt.gtExt_val σ hσ _ χ hJ).trans ((val_corr hJ (h₂.2 χ) _).trans ((val_pull hJ _ _ _).trans
        (congrArg (fun r => val (D.tau q.y χ) r y J) (TorusExt.extMap_jFK σ hσ))))⟩
  have hs : spMap f ≫ spMap σ = 𝟙 _ := by
    rw [← spMap_comp, h]; exact Spec.map_id (CommRingCat.of F')
  obtain ⟨b, v⟩ := (TorusExt.eq_gtExt_iff σ hσ q.g _).1 rfl
  refine ⟨⟨q.y, TorusExt.gtExt D σ hσ q.g, _, e₁, e₂⟩, rfl, ?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · show q.g.b.left = spMap f ≫ (TorusExt.gtExt D σ hσ q.g).b.left
    rw [b, ← Category.assoc, hs]
    exact (Category.id_comp _).symm
  · refine Eq.symm ((val_pull hJ _ _ _).trans ((val_corr hJ (v χ) _).trans ((val_pull hJ _ _ _).trans ?_)))
    exact congrArg (fun r => val (q.g.s χ) r y J) ((Category.assoc _ _ _).trans
      ((congrArg (𝟙 _ ≫ ·) hs).trans (Category.id_comp _)))

end General

section Dvr

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

theorem isOpenImmersion_generic : IsOpenImmersion (jK V) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : IsLocalization.Away ϖ (FractionRing V) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ


omit [IsDiscreteValuationRing V] in
theorem exists_fracInv : ∃ σ : FractionRing K →+* FractionRing V,
    (fracMap (IsFractionRing.injective V K)).comp σ = RingHom.id _ ∧
    σ.comp (fracMap (IsFractionRing.injective V K)) = RingHom.id _ := by
  let σ : FractionRing K ≃+* FractionRing V :=
    (FractionRing.algEquiv K K).toRingEquiv.trans (FractionRing.algEquiv V K).symm.toRingEquiv
  have h : σ.toRingHom.comp (fracMap (IsFractionRing.injective V K)) = RingHom.id _ :=
    IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun r => by
      show (FractionRing.algEquiv V K).symm (FractionRing.algEquiv K K (fracMap _ (algebraMap V _ r))) = algebraMap V _ r
      rw [fracMap_algebraMap, AlgEquiv.commutes]
      exact (FractionRing.algEquiv V K).symm.commutes r)
  exact ⟨σ.toRingHom, RingHom.ext fun x => σ.injective (RingHom.congr_fun h (σ x)), h⟩

variable {V K}

theorem exists_points {A : Over (Sp V)} {A' : Over (Sp K)} [GrpObj A] [GrpObj A'] [IsProper A.hom]
    {Φ : A'.left ⟶ A.left} (gp : IsGrpPullback A' A (spMap (algebraMap V K)) Φ) {X : Type} [Add X]
    (c : X → (𝟙_ (Over (Sp K)) ⟶ A')) (hc : ∀ a b, c (a + b) = c a * c b) :
    ∃ c₀ : X → (𝟙_ (Over (Sp V)) ⟶ A), (∀ a b, c₀ (a + b) = c₀ a * c₀ b) ∧
      ∀ x, (c x).left ≫ Φ = spMap (algebraMap V K) ≫ (c₀ x).left := by
  have hE : ValuativeCriterion.Existence A.hom := by
    have h : UniversallyClosed A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have ex : ∀ x, ∃ c₀ : 𝟙_ (Over (Sp V)) ⟶ A, (c x).left ≫ Φ = spMap (algebraMap V K) ≫ c₀.left := fun x => by
    let Q : ValuativeCommSq A.hom :=
      { R := V, K := K, i₁ := (c x).left ≫ Φ, i₂ := 𝟙 _, commSq := ⟨by
          rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w]
          exact (Category.id_comp _).trans (Category.comp_id _).symm⟩ }
    obtain ⟨⟨l, h1, h2⟩⟩ := hE Q
    exact ⟨Over.homMk l h2, h1.symm⟩
  choose c₀ h₀ using ex
  refine ⟨c₀, fun a b => ?_, h₀⟩
  have e : spMap (algebraMap V K) ≫ (c₀ (a + b)).left = spMap (algebraMap V K) ≫ (c₀ a * c₀ b).left := by
    rw [← h₀, hc]
    exact mul_push gp (T' := 𝟙_ _) (T := 𝟙_ _) _ (h₀ a) (h₀ b)
  let Q : ValuativeCommSq A.hom :=
    { R := V, K := K, i₁ := spMap (algebraMap V K) ≫ (c₀ (a + b)).left, i₂ := 𝟙 _,
      commSq := ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (c₀ (a + b))))⟩ }
  have := (IsSeparated.valuativeCriterion A.hom Q).elim ⟨(c₀ (a + b)).left, rfl, Over.w _⟩
    ⟨(c₀ a * c₀ b).left, e.symm, Over.w _⟩
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)

theorem exists_isPullDeg (hC : CubeSt) (P : PolAV (Sp V)) (D : DegPre K) (Φ : D.P.A.left ⟶ P.A.left)
    (gp : IsGrpPullback D.P.A P.A (spMap (algebraMap V K)) Φ) (hw₀ : LBIso D.P.L (P.L.pull Φ)) :
    ∃ (D₀ : DegPre V) (hD : IsPullDeg (algebraMap V K) D₀ D), D₀.P = P ∧ HEq (proj hD) Φ := by
  obtain ⟨w₀, hw₀⟩ := hw₀
  have hi := IsFractionRing.injective V K
  have := P.isAb.proper
  have := isOpenImmersion_generic V
  obtain ⟨c₀, cadd, hc⟩ := exists_points gp D.c D.c_add
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (hC _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P
  obtain ⟨w, hw, hr⟩ := TripleMap.exists_rigidified P.isLB D.P.isLB w₀ ((isGen_iff w₀).1 hw₀) (eSec P.A)
    (eSec D.P.A) D.P.A.hom (Over.w η[D.P.A]) (spMap (algebraMap V K)) (cubeMapOf gp).e_comm rig hrig D.rig D.rig_gen
  obtain ⟨σ, h₁, h₂⟩ := exists_fracInv V K
  let s : (TK V).left ⟶ (TK K).left := spMap σ
  have s₁ : genMap hi ≫ s = 𝟙 _ :=
    (spMap_comp _ _).symm.trans ((congrArg spMap h₁).trans (Spec.map_id (CommRingCat.of (FractionRing K))))
  have s₂ : s ≫ genMap hi = 𝟙 _ :=
    (spMap_comp _ _).symm.trans ((congrArg spMap h₂).trans (Spec.map_id (CommRingCat.of (FractionRing V))))
  have hx : ∀ χ, D.xK χ ≫ Φ = genMap hi ≫ ptK (c₀ χ) := fun χ => by
    show (jK K ≫ (D.c χ).left) ≫ Φ = genMap hi ≫ jK V ≫ (c₀ χ).left
    rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) ((Category.id_comp _).symm.trans (fracMap_sq hi))
  choose t ht vt using fun χ : D.X => exists_up hw P.isLB D.P.isLB (D.psi χ) (D.psi_gen χ)
  choose psi hpsi vpsi using fun χ : D.X => exists_gen P.isLB (K' := PUnit)
    (φ' := fun _ => ptK (c₀ χ)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (by
      show s ≫ D.xK χ ≫ Φ = _
      rw [hx, ← Category.assoc, s₂, Category.id_comp]))
    (LB.pullGen P.L _ _ (t χ) s) (DVR.pullGen_isGen _ _ _ _ (ht χ) s)
  let D₀ : DegPre V :=
    { P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c₀, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨ψW⟩ := nonempty_psiOn_generic D₀
  obtain ⟨hD, e⟩ := exists_isPullDeg_of_val hi D₀ D ψW (jK V).isoOpensRange.hom (jK V).isoOpensRange_hom_ι gp w hw hr
    (AddEquiv.refl _) hc (fun x z J J' hJ hJ' => by
      have v := vt x _ (𝟙 _) z _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
      refine (vpsi x _ _ z J hJ).trans ((val_pull hJ _ _ _).trans
        ((congrArg (fun r => val (t x) r z J) s₁).trans (v.trans (congrArg₂ (· * ·) ?_ rfl))))
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp])
  exact ⟨D₀, hD, rfl, heq_of_eq e⟩

theorem exists_isPullQk_surj (hG : GlobalFnsSt) {D₀ : DegPre V} {D : DegPre K} (hD : IsPullDeg (algebraMap V K) D₀ D)
    {k : ℕ} (q' : QkPt D (FractionRing K) k) : ∃ q, IsPullQk hD q q' := by
  have hi := IsFractionRing.injective V K
  letI : Algebra (FractionRing V) (FractionRing K) := (fracMap hi).toAlgebra
  have hK : Compat (algebraMap V K) (FractionRing K) := fracMap_algebraMap hi
  obtain ⟨σ, h₁, h₂⟩ := exists_fracInv V K
  obtain ⟨q, hy, hg⟩ := qkPullExists hG V K _ D₀ D hD (FractionRing K) hK k q'
  obtain ⟨p, hp⟩ := exists_qkExt_of_inverse (F := FractionRing V) (fracMap hi) σ h₁ h₂ q
  exact ⟨p, _, hK, q, hp, hy, hg⟩

end Dvr

end GlobalTheory.DvrDeg

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem GlobalTheory.DvrDeg.exists_extension : Known → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (Pv : Out.PolAV (Sp V)) (DK : Out.DegPre K) (φ : DK.P.A.left ⟶ Pv.A.left), IsPolFibre (algebraMap V K) Pv DK.P φ → ∃ (DV : Out.DegPre V) (p : Out.IsPullDeg (algebraMap V K) DV DK), DV.P = Pv ∧ HEq (prj p) φ ∧ ∀ (k : ℕ) (q' : Out.QkPt DK (FractionRing K) k), DK.TauBimult → ∃ q, GlobalTheory.ArcPull.IsPullQk p q q' := by
  intro hK V K _ _ _ _ _ _ Pv DK φ h
  obtain ⟨DV, p, h₁, h₂⟩ := GlobalTheory.DvrDeg.exists_isPullDeg hK.laws.cube Pv DK φ h.2.1 h.2.2.symm
  exact ⟨DV, p, h₁, h₂, fun k q' _ => GlobalTheory.DvrDeg.exists_isPullQk_surj hK.laws.globalFns p q'⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ.ExFr

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)

theorem one_eq : η[t'.G].left ≫ m.φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.one_left']
  have := m.cm.e_comm
  rw [m.base] at this
  exact this

theorem tan_iff (w : epsR S ⟶ t'.G) : IsTanAt x (w.left ≫ m.φ) ↔ IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (one_eq m).symm
    · have a : η[t'.G].left ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, hw, a, ← spMap_comp]
      have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
        ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      exact Spec.map_id _
  · intro h
    refine ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) h).trans (one_eq m)

theorem scale_over (s : S) : spMap (epsScaleR s) ≫ spMap (algebraMap S (DualNumber S)) =
    spMap (algebraMap S (DualNumber S)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem eig_iff (w : epsR S ⟶ t'.G) (a : 𝓞 E) (s : S) :
    (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ w.left ≫ m.φ ↔
      (w ≫ t'.act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc, m.act]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h
    · rw [Over.w, Category.assoc, hw, scale_over]; rfl
  · intro h
    rw [h, Category.assoc]; rfl

theorem exists_lift {T : Over (Sp S)} (v : T.left ⟶ Xo.univ.t.G.left) (hv : v ≫ Xo.univ.t.G.hom = T.hom ≫ x) :
    ∃ w : T ⟶ t'.G, w.left ≫ m.φ = v :=
  ⟨Over.homMk (m.cart.1.lift v T.hom hv) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

theorem push_prod {n : ℕ} (u : Fin n → (epsR S ⟶ t'.G)) :
    ((List.ofFn u).prod).left ≫ m.φ = ((List.ofFn fun i => pushHom m.cart (epsR S) (u i)).prod).left := by
  have := map_list_prod (pushHom m.cart (epsR S)) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact congrArg (fun q => q.left) this

theorem comb_iff {n : ℕ} (v : Fin n → (epsR S ⟶ t'.G)) (cf : Fin n → S) (w : epsR S ⟶ t'.G) :
    IsCombAt x (fun i => (v i).left ≫ m.φ) cf (w.left ≫ m.φ) ↔ IsLieComb cf v w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    choose u' hu' using fun i => exists_lift m (T := epsR S) (u i).left (Over.w (u i))
    have e : u = fun i => pushHom m.cart (epsR S) (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
    refine ⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩
    · apply m.cart.1.hom_ext
      · rw [Category.assoc]; exact (hu' i).trans (hu i)
      · have hv : (v i).left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w (v i)
        rw [Over.w, Category.assoc, hv, scale_over]; rfl
    · apply m.cart.1.hom_ext
      · rw [e] at hw
        exact hw.symm.trans (push_prod m u').symm
      · rw [Over.w, Over.w]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushHom m.cart (epsR S) (u i), fun i => ?_, (push_prod m u).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu, Category.assoc]; rfl

end GlobalTheory.ArcQ.ExFr


open GlobalTheory.ArcQ.ExFr in
theorem GlobalTheory.ArcQ.exists_isArcFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (z : Sp S ⟶ Xo.XF c), (ι.comp (PowerSeries.C (R := A))).Flat → z ≫ Y.j = spMap ι ≫ χ → z ≫ pullback.fst _ _ ≫ Xo.s = sOf c S → (∀ τ x, algebraMap c.F S (embK c τ x) = ι (PowerSeries.C (R := A) (ρ τ x))) → ∃ y : FrPt Xo c S, y.x = z ≫ pullback.fst _ _ ∧ IsArcFr W e th ι y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e th hB hth hA S _ _ ι z hfl hz hs hρ
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp S), Nonempty (SABMap t' Y.oF.t z) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull z Y.oF.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m1, hm1⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m m
  have cancel : ∀ (p : Sp S ⟶ Y.X) (_ : p = spMap ι ≫ χ) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' W.t (spMap ι), n.φ = m'.φ ≫ W.m.φ := by
    intro p hp n; subst hp; exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ W.m n
  obtain ⟨m2, hm2⟩ := cancel _ hz n
  open Matrix GlobalTheory.BasisUniv in
  have arcBasis_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
    intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e hB S _ ι hflat t' m2
    obtain ⟨v₀, hv₀, hB⟩ := hB
    obtain ⟨g, e₁, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.T.exists_constantLieBasis_arcGroup hG E H Dw l Xo c O β Y A b a χ W
    have hsm : Smooth W.t.G.hom := W.t.semi.smooth
    have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
    have hmon' : ∀ x, IsMonHom (t'.act.act x) := t'.act.hom
    obtain ⟨n, y, hy⟩ := Chart.univChartLoc W.t.G
    obtain ⟨n', y', hy'⟩ := exists_chart_of_pullback ι m2.cart
  
    have hU : ∀ τ k, ∃ U : Fin g → A, IsLieComb (fun j => PowerSeries.C (R := A) (U j)) v (v₀ τ k) := fun τ k => by
      have ht : GtTanR (e τ k) :=
        ((_root_.GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y A b a χ W (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1
      obtain ⟨U, hU, -⟩ := hcomb _ ht
      exact ⟨U, (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W g U e₁ (e τ k) v _ (fun i => (hev i).2) hU).1 (hv₀ τ k)⟩
    choose U hU using hU
    choose u hu using fun τ k => exists_lift ι m2.cart (v₀ τ k)
    choose v' hv' using fun j => exists_lift ι m2.cart (v j)
    have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange ι m2.cart hv hv'
    have hU' : ∀ τ k, IsLieComb (fun j => (ι.comp (PowerSeries.C (R := A))) (U τ k j)) v' (u τ k) := fun τ k =>
      Chart.comb_baseChange ι m2.cart (hU τ k) hv' (hu τ k)
    have hM' : ∀ x i, IsLieComb ((M x).map (ι.comp (PowerSeries.C (R := A))) i) v' (v' i ≫ t'.act.act x) := fun x i =>
      Chart.comb_baseChange ι m2.cart (hM x i) hv' (by
        rw [Over.comp_left, Category.assoc, m2.act, ← Category.assoc, hv', Category.assoc, Over.comp_left])
    have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
    have hUe : ∀ τ k x, U τ k ᵥ* M x = ρ τ x • U τ k := fun τ k x => by
      have := (eig_iff hy hv _ (hMR x) (hU τ k) _).1 (((hB τ).1 k).2 x)
      funext j
      have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
      simpa [Matrix.vecMul, dotProduct] using this
    refine ⟨u, fun τ k => ⟨v₀ τ k, hv₀ τ k, hu τ k⟩, fun τ => ⟨fun k => ⟨isTangent_of_comb hy' hb'.1 (hU' τ k), fun x => ?_⟩,
      fun w hw hwe => ?_⟩⟩
    · refine (eig_iff hy' hb' _ (hM' x) (hU' τ k) _).2 ?_
      funext j
      have := congrArg (ι.comp (PowerSeries.C (R := A))) (congrFun (hUe τ k x) j)
      simpa [Matrix.vecMul, dotProduct] using this
    · obtain ⟨z, hz, -⟩ := hb'.2 w hw
      simp only [comb_iff hy' hb' (hU' τ) hz]
      refine eig_powerSeries M (fun x => ρ τ x) (U τ) (hUe τ) (fun s hs => ?_) _ hflat z
        (fun x => (eig_iff hy' hb' _ (hM' x) hz _).1 (hwe x))
      have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
      have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
      simpa only [comb_iff hy hv (hU τ) hc] using this
  obtain ⟨u, hu1, hu2⟩ := arcBasis_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e hB S ι hfl t' m2
  obtain ⟨⟨θ, hθ, -⟩, -⟩ := GlobalTheory.existsUnique_thetaOf hL hL2 E H Dw l Xo c O β Y A b a χ W th hth
  have hnz := fun g => (GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres hL hL2 E H Dw l Xo c O β Y A b a χ W th θ hth hθ hA g).2
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w2).1 g2) W.t.PP.isLB t'.PP.isLB θ
  have hI2 : IsoMaps w2 σ' (thfPull W.t.PP.L m2.φ θ) := fun (i : PUnit → W.t.PP.L.ι) k => fn_ext fun y hy =>
    (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans
      ((hσ' _ (𝟙 _) y (i PUnit.unit) k (mem_pull.1 hy.1) hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))))))
  have nz := GlobalTheory.SectionBaseChange.fibre_nonzero_of_pull t'.PP.isLB hσ' m2.cart.1 hnz
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have hLB : LBIso t'.PP.L (Xo.univ.t.PP.L.pull m1.cm.F) := by
    obtain ⟨w, hw, -⟩ := m1.lin
    exact ⟨w, hw⟩
  have hgen := GlobalTheory.SectionBaseChange.generates hL.secBaseChange (GlobalTheory.Obj.toPolAV Xo.univ) m1.cart.1 t'.PP.isLB hLB σ' nz
  obtain ⟨s, w1, s1, r1, hI1, hg, hsgen⟩ := frame_of_gen Xo _ t' m1 σ' hgen
  have eig : ∀ (τ : E →+* ℂ) (w : epsR S ⟶ t'.G), IsEigAt c τ (w.left ≫ m1.φ) ↔
      ∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left :=
    fun τ w => forall_congr' fun x => by rw [← hρ]; exact eig_iff m1 w x _
  refine ⟨⟨z ≫ pullback.fst _ _, (Category.assoc _ _ _).trans hs, fun τ k => (u τ k).left ≫ m1.φ,
    fun τ k => (tan_iff m1 _).2 ((hu2 τ).1 k).1, fun τ k => (eig τ _).2 ((hu2 τ).1 k).2, fun τ w hw hw' => ?_,
    s, hsgen⟩, rfl, z, t', m1, m2, m.φ, hz, rfl, m.cart.1.w, hm1.symm, hn.symm.trans hm2, fun τ k => ?_,
    θ, w1, w2, σ', s1, _, hθ, r1, ⟨g2, r2⟩, hI1, hI2, fun _ _ => rfl, hg⟩
  · obtain ⟨w', rfl⟩ := exists_lift m1 (T := epsR S) w hw.1
    exact (existsUnique_congr fun cf => comb_iff m1 (u τ) cf w').2
      ((hu2 τ).2 w' ((tan_iff m1 w').1 hw) ((eig τ w').1 hw'))
  · obtain ⟨v, hv, hv'⟩ := hu1 τ k
    exact ⟨v, (u τ k).left, hv, rfl, hv', Over.w (u τ k)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyChainArcWitnessUniversalFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_chain_arc_witness_universal_family : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) , χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β) → (∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Nonempty (Chain W Λ) := by
  first | exact @GlobalTheory.ArcPts.nonempty_chain | exact GlobalTheory.ArcPts.nonempty_chain | (intros; apply GlobalTheory.ArcPts.nonempty_chain <;> assumption)
end

