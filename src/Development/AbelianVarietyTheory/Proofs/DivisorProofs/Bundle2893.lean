module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldBasisToroidalModelSnc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
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
open GlobalTheory.TangentOrigin

noncomputable section
namespace GlobalTheory.VertCoeffRing

theorem isLieBasis_tvE : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  intro R _ G _ _ n v
  have hE : (overAt (𝟙 (Sp R)) (DualNumber R)).hom = (epsR R).hom := by
    simp [epsR, overAt]
  let e : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (𝟙 _) (by simp [hE])
  let f : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ epsR R := Over.homMk (𝟙 _) (by simp [hE])
  have hfe : f ≫ e = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])
  have hef : e ≫ f = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])

  have htv : ∀ x : TanM (𝟙 (Sp R)) G, tvE x = e ≫ tv x := by
    intro x
    apply Over.OverMorphism.ext
    first
    | (simp only [e, Over.comp_left, Over.homMk_left, Category.id_comp]; exact tvE_left x)
    | simp [e, tvE_left x]
  have hadd : ∀ x y : TanM (𝟙 (Sp R)) G, tvE (x + y) = tvE x * tvE y := by
    intro x y; rw [htv, htv, htv, PullbackSections.tv_add, MonObj.comp_mul]
  have hzero : tvE (0 : TanM (𝟙 (Sp R)) G) = 1 := by
    rw [htv, PullbackSections.tv_zero, MonObj.comp_one]

  have hsmul : ∀ (a : R) (x : TanM (𝟙 (Sp R)) G),
      (tvE (a • x)).left = spMap (epsScaleR a) ≫ (tvE x).left := by
    intro a x; rw [tvE_left, tvE_left, PullbackSections.tv_smul]
    first
    | rfl
    | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
  have hinj : ∀ x y : TanM (𝟙 (Sp R)) G, tvE x = tvE y → x = y := by
    intro x y h
    apply PullbackSections.tanM_ext
    have h' := congrArg (fun t => f ≫ t) h
    simpa [htv, ← Category.assoc, hfe] using h'
  have hsum : ∀ (c : Fin n → R) (s : Finset (Fin n)),
      tvE (∑ i ∈ s, c i • v i) = ∏ i ∈ s, tvE (c i • v i) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]

  have hcomb : ∀ (c : Fin n → R) (w : epsR R ⟶ G),
      IsLieComb c (fun a => tvE (v a)) w ↔ w = tvE (∑ i, c i • v i) := by
    intro c w
    rw [IsLieComb.eq_1, hsum]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [List.prod_ofFn]
      refine Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext ?_
      rw [hu i, hsmul]
    · rintro rfl
      exact ⟨fun i => tvE (c i • v i), fun i => hsmul _ _, by rw [List.prod_ofFn]⟩

  have hfa : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp
  have hdual : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    simp only [spMap.eq_1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id]
    all_goals rfl
  have hz : spMap (epsScaleR (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have h0 : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
      refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
      all_goals first
        | (simp [epsScaleR]; done)
        | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done)
        | (simp [epsScaleR.eq_1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fstHom_apply,
            TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]; done)
        | rfl
        | (simp [epsScaleR]; rfl)
    rw [h0]
    simp only [spMap.eq_1, CommRingCat.ofHom_comp, Spec.map_comp]
  have hu : (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left = spMap (algebraMap R (DualNumber R)) := by
    first
    | simp [overAt]
    | (have h := Over.w (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))); simpa [overAt] using h)
  have hone : (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left =
      spMap (algebraMap R (DualNumber R)) ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := by
    calc (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left
        = (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := rfl
      _ = _ := by rw [hu]

  have key : ∀ g : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, smT (𝟙 (Sp R)) 0 g = 1 ↔ IsTangent (e ≫ g) := by
    intro g
    rw [IsTangent.eq_1]
    have hl : (smT (𝟙 (Sp R)) 0 g).left = spMap (algebraMap R (DualNumber R)) ≫
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g.left := by
      rw [← Category.assoc, ← hz]
      first
      | rfl
      | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
    have he : ∀ t : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (e ≫ t).left =
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t.left := by
      intro t; simp [e]
    rw [he]
    constructor
    · intro h
      have h2 := congrArg Over.Hom.left h
      rw [hl, hone] at h2
      have h3 := congrArg (fun t => spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t) h2
      simpa only [← Category.assoc, hdual, Category.id_comp] using h3
    · intro h
      apply Over.OverMorphism.ext
      rw [hl, hone, h]
  have htan : ∀ x, IsTangent (tvE x) := fun x => by
    rw [htv]; exact (key (tv x)).1 (PullbackSections.tv_mem x)
  have hsurj : ∀ w : epsR R ⟶ G, IsTangent w → ∃ x, tvE x = w := by
    intro w hw
    have hw' : IsTangent (e ≫ (f ≫ w)) := by rwa [← Category.assoc, hef, Category.id_comp]
    refine ⟨PullbackSections.mkT (f ≫ w) ((key _).2 hw'), ?_⟩
    rw [htv, PullbackSections.tv_mkT, ← Category.assoc, hef, Category.id_comp]
  rw [IsLieBasis.eq_1]
  refine ⟨fun i => htan (v i), fun w hw => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj w hw
  refine ⟨⇑(v.repr x), (hcomb _ _).2 ?_, fun c hc => ?_⟩
  · rw [v.sum_repr]
  · have h := hinj _ _ ((hcomb c _).1 hc)
    rw [h, v.repr_sum_self]

end GlobalTheory.VertCoeffRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizedModuleRes
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
open GlobalTheory.LogDerProj

namespace GlobalTheory.LogDerProj

theorem isLocalizedModule_res : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ J : Ideal R, IsLocalizedModule (Submonoid.powers f) (res (S := S) f φ J) := by
  intro k R S _ _ _ _ f _ φ hφ J
  refine IsLocalizedModule.mk (fun x => ?_) (GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway f φ hφ J) (GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq f φ hφ J _ _)
  have hu : IsUnit (algebraMap R S x) := IsLocalization.map_units S x
  rw [Module.End.isUnit_iff]
  constructor
  · intro n n' h
    have h' : algebraMap R S x • n.1 = algebraMap R S x • n'.1 := by
      simpa [algebraMap_smul] using congrArg Subtype.val h
    exact Subtype.ext ((hu.smul_left_cancel).1 h')
  · intro n
    refine ⟨⟨((hu.unit⁻¹ : Sˣ) : S) • n.1, (show _ ∈ logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S)) from
      Submodule.smul_mem _ _ n.2)⟩, Subtype.ext ?_⟩
    change (x : R) • (((hu.unit⁻¹ : Sˣ) : S) • n.1) = n.1
    rw [← algebraMap_smul S (x : R), smul_smul, IsUnit.mul_val_inv, one_smul]

theorem finrank_fibre : ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (f : R) (d : ℕ) (ϕ : M →ₗ[R] (Fin d → Localization.Away f)), IsLocalizedModule (Submonoid.powers f) ϕ → ∀ m : Ideal R, m.IsMaximal → f ∉ m → Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = d := by
  intro R M _ _ _ f d ϕ hϕ m hm hf
  letI := Ideal.Quotient.field m
  have hu : IsUnit (algebraMap R (R ⧸ m) f) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf
  letI : Algebra (Localization.Away f) (R ⧸ m) := (IsLocalization.Away.lift f hu).toAlgebra
  haveI : IsScalarTower R (Localization.Away f) (R ⧸ m) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hbc : IsBaseChange (Localization.Away f) ϕ := IsLocalizedModule.isBaseChange (Submonoid.powers f) _ ϕ
  let e1 := hbc.equiv
  let e2 := TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away f) (R ⧸ m) (R ⧸ m) M
  let e3 := LinearEquiv.baseChange (Localization.Away f) (R ⧸ m) _ _ e1
  rw [← e2.finrank_eq, e3.finrank_eq, Module.finrank_eq_card_basis
    (Algebra.TensorProduct.basis (R ⧸ m) (Pi.basisFun (Localization.Away f) (Fin d))), Fintype.card_fin]

end GlobalTheory.LogDerProj


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LogDerProj.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ U : Y.X.affineOpens, Module.Finite Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) ∧ Module.Projective Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U
  haveI : SmoothOfRelativeDimension Dw.dim Y.s := smooth_gen_iff.1 hsm
  haveI : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  set I := Scheme.IdealSheafData.vanishingIdeal (interior Y).compl with hI
  let φ : c.F →+* Γ(Y.X, U.1) := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.s U.1
  have hφ : φ.FiniteType := by
    have h1 : (Y.s.appLE ⊤ U.1 (by simp)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType Y.s inferInstance ⟨⊤, isAffineOpen_top _⟩ U _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.surjective)
  have hM : logDer Y.s I U = GlobalTheory.LogDerProj.logSub φ (I.ideal U) := rfl
  have loc : ∀ q : PrimeSpectrum Γ(Y.X, U.1), ∃ r ∉ q.asIdeal,
      ∃ ϕ : GlobalTheory.LogDerProj.logSub φ (I.ideal U) →ₗ[Γ(Y.X, U.1)] (Fin Dw.dim → Localization.Away r),
        IsLocalizedModule (Submonoid.powers r) ϕ := by
    intro q
    have hU : IsAffineOpen U.1 := U.2
    have hxU : hU.fromSpec q ∈ U.1 := by
      change _ ∈ (U.1 : Set Y.X)
      rw [← hU.range_fromSpec]
      exact ⟨q, rfl⟩
    have key := _root_.GlobalTheory.LogBasis.exists_logDer_basis E H Dw l Xo c Y h1 hsm hsnc U (hU.fromSpec q) hxU
    obtain ⟨f, W, hW, m, t, b, hxW, hWf, -⟩ := key
    have hq : f ∉ q.asIdeal := by
      have : q ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen f := by rw [← hWf]; exact hxW
      rw [hU.fromSpec_preimage_basicOpen] at this
      exact this
    letI : Algebra Γ(Y.X, U.1) Γ(Y.X, W.1) := (Y.X.presheaf.map (homOfLE hW).op).hom.toAlgebra
    have hloc : ∀ (V : Y.X.Opens) (hV : V ≤ U.1), V = Y.X.basicOpen f →
        letI := (Y.X.presheaf.map (homOfLE hV).op).hom.toAlgebra; IsLocalization.Away f Γ(Y.X, V) := by
      rintro V hV rfl
      exact U.2.isLocalization_basicOpen f
    haveI : IsLocalization.Away f Γ(Y.X, W.1) := hloc W.1 hW hWf
    have hc : ∀ a, algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1) (φ a) = constFn Y.s W.1 a :=
      fun a => congr(($(Scheme.Hom.appLE_map Y.s (U := ⊤) (V := U.1) (fun _ _ => trivial) (homOfLE hW).op)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a))
    have hid : (I.ideal U).map (algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1)) = I.ideal W := I.map_ideal (U := W) (V := U) hW
    have hN : logDer Y.s I W = GlobalTheory.LogDerProj.logSub
        ((algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1)).comp φ) ((I.ideal U).map (algebraMap _ _)) := by
      ext D
      rw [GlobalTheory.LogDerProj.mem_logSub, hid]
      simp only [RingHom.comp_apply, hc]
      rfl
    let b' := b.map (LinearEquiv.ofEq _ _ hN)
    let e := (b'.equivFun.restrictScalars Γ(Y.X, U.1)).trans (LinearEquiv.piCongrRight fun _ =>
      (IsLocalization.algEquiv (Submonoid.powers f) Γ(Y.X, W.1) (Localization.Away f)).toLinearEquiv)
    haveI := GlobalTheory.LogDerProj.isLocalizedModule_res (S := Γ(Y.X, W.1)) f φ hφ (I.ideal U)
    exact ⟨f, hq, e.toLinearMap ∘ₗ GlobalTheory.LogDerProj.res (S := Γ(Y.X, W.1)) f φ (I.ideal U),
      IsLocalizedModule.of_linearEquiv (Submonoid.powers f) (GlobalTheory.LogDerProj.res (S := Γ(Y.X, W.1)) f φ (I.ideal U)) e⟩
  rw [hM]
  obtain ⟨hfin, hproj⟩ := GlobalTheory.LocFreeProj.finite_projective_of_locally_free _ _ fun q => by
    obtain ⟨r, hr, ϕ, hϕ⟩ := loc q
    exact ⟨r, hr, Fin Dw.dim → Localization.Away r, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ϕ, hϕ⟩
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  obtain ⟨r, hr, ϕ, hϕ⟩ := loc ⟨m, hm.isPrime⟩
  exact GlobalTheory.LogDerProj.finrank_fibre r Dw.dim ϕ hϕ m hm hr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenEigenRankLevelSetIntegersAction
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

namespace GlobalTheory.BalProjOpen

open GlobalTheory.BalProj

theorem eigSp_eq_range {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k)
    (P : Matrix (Fin n) (Fin n) k) (hP : ∀ a, P * B a = χ a • P) (hfix : ∀ c ∈ eigSp B χ, c ᵥ* P = c) :
    eigSp B χ = LinearMap.range (Matrix.vecMulLinear P) := by
  ext c
  constructor
  · intro hc
    exact ⟨c, hfix c hc⟩
  · rintro ⟨d, rfl⟩ a
    show (d ᵥ* P) ᵥ* B a = χ a • (d ᵥ* P)
    rw [Matrix.vecMul_vecMul, hP a, Matrix.vecMul_smul]

theorem finrank_range_eq_trace {k : Type} [Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k) (hP : P * P = P) :
    (Module.finrank k (LinearMap.range (Matrix.vecMulLinear P)) : k) = P.trace := by
  have h1 : Matrix.vecMulLinear P = Matrix.toLin' Pᵀ := by
    ext c i
    simp [Matrix.mulVec_transpose]
  have hi : IsIdempotentElem (Matrix.toLin' Pᵀ) := by
    show Matrix.toLin' Pᵀ * Matrix.toLin' Pᵀ = Matrix.toLin' Pᵀ
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.transpose_mul, hP]
  rw [h1, ← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace, Matrix.trace_toLin'_eq, Matrix.trace_transpose]

theorem eigRank_cast_eq_trace {O R k : Type} [CommRing O] [CommRing R] [Field k] (φ : R →+* k) {n : ℕ}
    (A : O → Matrix (Fin n) (Fin n) R) (hmul : ∀ a b, A (a * b) = A a * A b) (χ : O → R)
    {J : Type} [Fintype J] (f : J → R) (b : J → O) (h1 : ∑ i, f i * χ (b i) = 1)
    (h2 : ∀ a, ∑ i, f i • A (a * b i) = χ a • ∑ i, f i • A (b i)) :
    (eigRank φ A χ : k) = φ (∑ i, f i • A (b i)).trace := by
  set P := ∑ i, f i • A (b i) with hPdef
  have hPA : ∀ a, P * A a = χ a • P := by
    intro a
    rw [← h2 a, hPdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, ← hmul, mul_comm]
  have hPP : P * P = P := by
    conv_lhs => arg 2; rw [hPdef]
    rw [Finset.mul_sum]
    simp_rw [mul_smul_comm, hPA, smul_smul, ← Finset.sum_smul, h1, one_smul]
  set Pb := P.map φ
  have hPbA : ∀ a, Pb * (A a).map φ = φ (χ a) • Pb := by
    intro a
    rw [← Matrix.map_mul, hPA a]
    ext i j
    simp [Pb]
  have hfix : ∀ c ∈ eigSp (fun a => (A a).map φ) (fun a => φ (χ a)), c ᵥ* Pb = c := by
    intro c hc
    have : Pb = ∑ i, φ (f i) • (A (b i)).map φ := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Pb, hPdef, Matrix.sum_apply, map_sum]
    rw [this, Matrix.vecMul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [Matrix.vecMul_smul, hc _, smul_smul, ← Finset.sum_smul, ← map_mul, ← map_sum, h1, map_one, one_smul]
  have hPbPb : Pb * Pb = Pb := by rw [← Matrix.map_mul, hPP]
  unfold eigRank
  rw [eigSp_eq_range _ _ Pb hPbA hfix, finrank_range_eq_trace Pb hPbPb]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Pb, Matrix.trace, map_sum]

theorem isOpen_eigRank_eq_of_datum {O R K : Type} [CommRing O] [CommRing R] [Field K] [CharZero K] (j : K →+* R)
    {n : ℕ} (A : O → Matrix (Fin n) (Fin n) R) (hmul : ∀ a b, A (a * b) = A a * A b) (χ : O → R)
    {J : Type} [Fintype J] (f : J → R) (b : J → O) (h1 : ∑ i, f i * χ (b i) = 1)
    (h2 : ∀ a, ∑ i, f i • A (a * b i) = χ a • ∑ i, f i • A (b i)) (N : ℕ) :
    IsOpen {𝔭 : PrimeSpectrum R | eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = N} := by
  set t := (∑ i, f i • A (b i)).trace with ht
  have key : ∀ (𝔭 : PrimeSpectrum R) (M : ℕ),
      eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = M ↔ t - M ∈ 𝔭.asIdeal := by
    intro 𝔭 M
    haveI : CharZero 𝔭.asIdeal.ResidueField :=
      (RingHom.charZero_iff ((algebraMap R 𝔭.asIdeal.ResidueField).comp j).injective).1 inferInstance
    rw [← Nat.cast_inj (R := 𝔭.asIdeal.ResidueField), eigRank_cast_eq_trace _ A hmul χ f b h1 h2,
      ← Ideal.algebraMap_residueField_eq_zero, map_sub, map_natCast, sub_eq_zero]
  have hle : ∀ 𝔭 : PrimeSpectrum R, eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ ≤ n := by
    intro 𝔭
    unfold eigRank
    exact (Submodule.finrank_le _).trans (by simp)
  have hset : {𝔭 : PrimeSpectrum R | eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = N} =
      (⋃ M ∈ (Finset.range (n + 1)).filter (· ≠ N), PrimeSpectrum.zeroLocus {t - (M : R)})ᶜ := by
    ext 𝔭
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, exists_prop, not_exists, not_and]
    constructor
    · intro h M hM hM'
      exact hM.2 (((key 𝔭 M).2 hM').symm.trans h)
    · intro h
      by_contra hne
      exact h _ ⟨Nat.lt_succ_of_le (hle 𝔭), hne⟩ ((key 𝔭 _).1 rfl)
  rw [hset]
  exact (isClosed_biUnion_finset fun M _ => PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

theorem exists_datum {E : Type} [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ)
    (A : 𝓞 E → Matrix (Fin n) (Fin n) R) (hadd : ∀ a b, A (a + b) = A a + A b) (τ : E →+* ℂ) :
    ∃ (J : Type) (_ : Fintype J) (f : J → R) (b : J → 𝓞 E),
      ∑ i, f i * embR F hF iF τ (b i) = 1 ∧
      ∀ a, ∑ i, f i • A (a * b i) = embR F hF iF τ a • ∑ i, f i • A (b i) := by
  classical
  set bO := RingOfIntegers.basis E
  set bE := integralBasis E
  have hnd := _root_.traceForm_nondegenerate ℚ E
  obtain ⟨d, hd⟩ : ∃ d, d = (Algebra.traceForm ℚ E).dualBasis hnd bE := ⟨_, rfl⟩
  have hdr : ∀ i j, Algebra.trace ℚ E (bE i * d j) = if i = j then 1 else 0 := by
    intro i j
    rw [← Algebra.traceForm_apply, hd]
    exact LinearMap.BilinForm.apply_dualBasis_right hnd (Algebra.traceForm_isSymm ℚ) bE i j
  have hdrep0 : ∀ (y : E) i, d.repr y i = Algebra.trace ℚ E (y * bE i) := by
    intro y i
    rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  set g : E →+* R := iF.comp (τ.codRestrict F.toSubfield (hF τ))
  have hg : ∀ a : 𝓞 E, embR F hF iF τ a = g (a : E) := fun a => rfl
  have hbE : ∀ i, bE i = (bO i : E) := fun i => integralBasis_apply E i
  have hrep : ∀ (y : E) i, bE.repr y i = Algebra.trace ℚ E (y * d i) := by
    intro y i
    conv_rhs => rw [← bE.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, map_smul, hdr, smul_eq_mul, mul_ite, _root_.mul_one]
    simp
  have hdrep : ∀ y : E, y = ∑ i, Algebra.trace ℚ E (y * bE i) • d i := by
    intro y
    conv_lhs => rw [← d.sum_repr y]
    simp_rw [hdrep0]
  have hA : ∑ i, d i * bE i = 1 := by
    rw [← sub_eq_zero]
    refine hnd.1 _ fun y => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Algebra.traceForm_apply, sub_mul, map_sub, _root_.one_mul, Finset.sum_mul, map_sum, sub_eq_zero,
      Algebra.trace_eq_matrix_trace bE y, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrep]
    congr 1
    ring
  have hB : ∀ (a : 𝓞 E) j, ∑ i, ((bO.repr (a * bO i) j : ℤ) : E) * d i = (a : E) * d j := by
    intro a j
    conv_rhs => rw [hdrep ((a : E) * d j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Algebra.trace ℚ E ((a : E) * d j * bE i) = bE.repr ((a : E) * bE i) j := by
      rw [hrep]; congr 1; ring
    have h2 : bE.repr ((a : E) * bE i) j = ((bO.repr (a * bO i) j : ℤ) : ℚ) := by
      rw [hbE]
      exact integralBasis_repr_apply E (a * bO i) j
    rw [h1, h2, Algebra.smul_def, eq_ratCast, Rat.cast_intCast]
  have hexp : ∀ x : 𝓞 E, A x = ∑ j, bO.repr x j • A (bO j) := by
    intro x
    let Aa : 𝓞 E →+ Matrix (Fin n) (Fin n) R := AddMonoidHom.mk' A hadd
    conv_lhs => rw [← bO.sum_repr x]
    exact (map_sum Aa _ _).trans (Finset.sum_congr rfl fun j _ => map_zsmul Aa _ _)
  refine ⟨_, inferInstance, fun i => g (d i), bO, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp_rw [hg, ← map_mul, ← map_sum, ← hbE, hA, map_one]
  · intro a
    calc ∑ i, g (d i) • A (a * bO i)
        = ∑ i, ∑ j, (g (d i) * ((bO.repr (a * bO i) j : ℤ) : R)) • A (bO j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hexp (a * bO i), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← smul_smul, Int.cast_smul_eq_zsmul]
      _ = ∑ j, (∑ i, g (d i) * ((bO.repr (a * bO i) j : ℤ) : R)) • A (bO j) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_smul]
      _ = ∑ j, (embR F hF iF τ a * g (d j)) • A (bO j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          set_option synthInstance.maxHeartbeats 100000 in
            rw [hg, ← map_mul, ← hB a j, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul g, map_intCast g, _root_.mul_comm]
      _ = _ := by
          rw [Finset.smul_sum]
          simp_rw [smul_smul]

theorem isOpen_eigRank_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → ∀ (τ : E →+* ℂ) (N : ℕ), IsOpen {𝔭 : PrimeSpectrum R | GlobalTheory.BalProj.eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) = N} := by
  intro E _ _ _ F hF R _ iF n A h1 hadd hmul τ N
  obtain ⟨J, _, f, b, hf1, hf2⟩ := exists_datum F hF R iF n A hadd τ
  exact isOpen_eigRank_eq_of_datum iF A hmul _ f b hf1 hf2 N

end GlobalTheory.BalProjOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanDeRhamHomologyRankTwoG
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PeriodSpan

theorem main : PSpan := by
  intro A _ g hA _ L u P hP
  exact _root_.GlobalTheory.CechPer.span_periods_eq_top_and_finrank A g L u hA P fun c =>
    GlobalTheory.T.crystalline_period_eq_cechDeRham_period A g L u c.1
      { toFun := fun l => P l c, map_zero' := by simp, map_add' := fun x y => by simp }
      _ (fun _ => rfl) (hP c)

end GlobalTheory.PeriodSpan
end

