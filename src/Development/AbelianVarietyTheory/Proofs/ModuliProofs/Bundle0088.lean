module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem cubicalStr_of_triv_theta : Out.Laws → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.Rigidified A M → Triv (Theta A M) → ∃ L : RigLB A, L.L = M ∧ Nonempty (CubicalStr A L) := by
  intro hL S A _ _ hA M hM hR hT
  obtain ⟨t, ht⟩ := hT
  obtain ⟨r, hr⟩ := hR
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised hM t ht
  exact ⟨⟨M, r, hM, hr⟩, rfl, ⟨GlobalTheory.AbLaw.Cube.cubicalOfNormalised
    (by cases hL; assumption) hA ⟨M, r, hM, hr⟩ t' ht' hn⟩⟩

end GlobalTheory.Moduli
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

section Deriv

open GlobalTheory.TangentOrigin GlobalTheory.LieEtale

variable {g g' : ℕ} {X Y : Scheme.{0}}

theorem evalPt_comp {R : Type} [CommRing R] (x : Sp R ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evalPt (x ≫ φ) U h f = evalPt x (φ ⁻¹ᵁ U) h ((φ.app U).hom f) := by
  have := Scheme.Hom.appLE_comp_appLE x φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h
  unfold evalPt
  rw [← this, Scheme.Hom.app_eq_appLE]
  rfl

theorem valAt'_comp (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · rw [valAt'_eq_evalPt _ _ h, valAt'_eq_evalPt x (φ ⁻¹ᵁ U) h, evalPt_comp]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    unfold valAt'
    rw [dite_eq_right h, dite_eq_right h']

theorem isHolTo_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e) (φ : X ⟶ Y) :
    IsHolTo Set.univ fun z => e z ≫ φ := by
  intro U f
  simp only [valAt'_comp]
  exact he (φ ⁻¹ᵁ U) ((φ.app U).hom f)

theorem isHolTo_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : IsHolTo Set.univ fun z => e (F z) := by
  intro U f
  have hF : Differentiable ℂ F := F.toContinuousLinearMap.differentiable
  exact ⟨(he U f).1.preimage hF.continuous, (he U f).2.comp hF.differentiableOn fun z hz => hz⟩

theorem isDerivAt0_iff {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 e w v ↔ spMap fstC ≫ v = e 0 ∧ ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      (evalPt v U h f).snd = fderiv ℂ (fun z => valAt' (e z) U f) 0 w := Iff.rfl

theorem deriv_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (φ : X ⟶ Y) : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  rw [isDerivAt0_iff] at h ⊢
  refine ⟨by rw [← h.1, Category.assoc], fun U hU f => ?_⟩
  simp only [valAt'_comp]
  rw [evalPt_comp]
  exact h.2 _ _ _

theorem deriv_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (h' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at h h'
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e 0 (default : PrimeSpectrum ℂ))) isOpen_univ
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := fun q _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) q default]; exact hx
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (h.1 ▸ h0)
  have hv' : ⊤ ≤ v' ⁻¹ᵁ U := (top_le_preimage_iff v' U).2 (h'.1 ▸ h0)
  refine ext_evalPt hU hv hv' (RingHom.ext fun f => TrivSqZeroExt.ext ?_ ((h.2 U hv f).trans (h'.2 U hv' f).symm))
  have key : ∀ (u : Sp (DualNumber ℂ) ⟶ X) (hu : ⊤ ≤ u ⁻¹ᵁ U) (y : Sp ℂ ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      spMap fstC ≫ u = y → (evalPt u U hu f).fst = evalPt y U hy f := by
    rintro u hu y hy rfl
    exact (evalPt_spMap_comp fstC u U hu hy f).symm
  exact (key v hv _ h0 h.1).trans (key v' hv' _ h0 h'.1).symm

theorem deriv_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 (fun z => e (F z)) w v ↔ IsDerivAt0 e (F w) v := by
  rw [isDerivAt0_iff, isDerivAt0_iff, map_zero]
  refine and_congr_right fun h0 => forall₃_congr fun U hU f => ?_
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h0 ▸ (top_le_preimage_iff v U).1 hU
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (F.toContinuousLinearMap 0) := by
    rw [map_zero]
    exact (he U f).2.differentiableAt ((he U f).1.mem_nhds ⟨trivial, hU0⟩)
  have := (hd.hasFDerivAt.comp 0 F.toContinuousLinearMap.hasFDerivAt).fderiv
  rw [map_zero] at this
  have e2 : fderiv ℂ (fun z => valAt' (e (F z)) U f) 0 = _ := this
  rw [e2]
  rfl

theorem deriv_smul {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (c : ℂ) : IsDerivAt0 e (c • w) (spMap (epsScale c) ≫ v) := by
  rw [isDerivAt0_iff] at h ⊢
  have e0 : spMap fstC ≫ spMap (epsScale c) ≫ v = spMap fstC ≫ v := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r
  refine ⟨e0.trans h.1, fun U hU f => ?_⟩
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (e0 ▸ (top_le_preimage_iff _ U).1 hU)
  rw [evalPt_spMap_comp _ v U hv hU, map_smul, ← h.2 U hv f]
  simp [epsScale]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

abbrev epsTwo (y : Sp ℂ ⟶ S) : Over S := Over.mk (spMap (algebraMap ℂ (TrivSqZeroExt ℂ (ℂ × ℂ))) ≫ y)

def toTwo (y : Sp ℂ ⟶ S) (l : ℂ →ₗ[ℂ] ℂ × ℂ) : epsTwo y ⟶ epsPt y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

def ofTwo (y : Sp ℂ ⟶ S) (l : ℂ × ℂ →ₗ[ℂ] ℂ) : epsPt y ⟶ epsTwo y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

theorem ofTwo_toTwo (l : ℂ →ₗ[ℂ] ℂ × ℂ) (l' : ℂ × ℂ →ₗ[ℂ] ℂ) :
    ofTwo y l' ≫ toTwo y l = epsPtScale y (l' (l 1)) := by
  refine Over.OverMorphism.ext ?_
  change spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [this, epsScale]

theorem epsPtScale_one : epsPtScale y 1 = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  change spMap _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  ext x <;> simp [epsScale]

theorem epsPtScale_zero {v : epsPt y ⟶ G} (hv : epsPtZero y ≫ v = 1) : epsPtScale y 0 ≫ v = 1 := by
  let s : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have : epsPtScale y 0 = s ≫ epsPtZero y := by
    refine Over.OverMorphism.ext ?_
    change spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this, Category.assoc, hv, MonObj.comp_one]

theorem deriv_mul {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (h0 : e 0 = (1 : Over.mk y ⟶ G).left)
    (h : IsDerivAt0 e w v.left) (h' : IsDerivAt0 e w' v'.left) : IsDerivAt0 e (w + w') (v * v').left := by
  have hv : epsPtZero y ≫ v = 1 := Over.OverMorphism.ext (h.1.trans h0)
  have hv' : epsPtZero y ≫ v' = 1 := Over.OverMorphism.ext (h'.1.trans h0)
  have hm : epsPtZero y ≫ (v * v') = 1 := by rw [MonObj.comp_mul, hv, hv', _root_.mul_one]
  have hm' : spMap fstC ≫ (v * v').left = e 0 := (congrArg (·.left) hm).trans h0.symm
  rw [isDerivAt0_iff] at h h' ⊢
  refine ⟨hm', fun U hU f => ?_⟩
  let u : epsTwo y ⟶ G := (toTwo y (LinearMap.inl ℂ ℂ ℂ) ≫ v) * (toTwo y (LinearMap.inr ℂ ℂ ℂ) ≫ v')
  have hu : ∀ l, ofTwo y l ≫ u = (epsPtScale y (l (1, 0)) ≫ v) * (epsPtScale y (l (0, 1)) ≫ v') := fun l => by
    simp only [u, MonObj.comp_mul, ← Category.assoc, ofTwo_toTwo]
    rfl
  have h1 : ofTwo y (LinearMap.fst ℂ ℂ ℂ) ≫ u = v := by
    rw [hu, LinearMap.fst_apply, LinearMap.fst_apply, epsPtScale_one, epsPtScale_zero hv', _root_.mul_one, Category.id_comp]
  have h2 : ofTwo y (LinearMap.snd ℂ ℂ ℂ) ≫ u = v' := by
    rw [hu, LinearMap.snd_apply, LinearMap.snd_apply, epsPtScale_one, epsPtScale_zero hv, _root_.one_mul, Category.id_comp]
  have h3 : ofTwo y (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) ≫ u = v * v' := by
    rw [hu]; simp [epsPtScale_one]
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := hm' ▸ (top_le_preimage_iff _ U).1 hU
  have hU1 : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h.1 ▸ hU0)
  have hU2 : ⊤ ≤ v'.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h'.1 ▸ hU0)
  have hsub : ∀ p q : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), p = q := by
    have k : ∀ z : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
      constructor
      · intro ha
        by_contra h0
        exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
      · intro ha
        refine z.2.mem_of_pow_mem 2 ?_
        rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
        exact z.asIdeal.zero_mem
    intro p q
    ext a
    rw [k, k]
  have hUu : ⊤ ≤ u.left ⁻¹ᵁ U := fun p _ => by
    let q : (epsPt y).left := spMap fstC (default : PrimeSpectrum ℂ)
    have hq : v.left q ∈ U := hU1 (Set.mem_univ q)
    rw [← h1] at hq
    rw [hsub p ((ofTwo y (LinearMap.fst ℂ ℂ ℂ)).left q)]
    exact hq
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (x : epsPt y ⟶ G) (hx : ⊤ ≤ x.left ⁻¹ᵁ U), ofTwo y l ≫ u = x →
      (evalPt (R := DualNumber ℂ) x.left U hx f).snd =
        l (evalPt (R := TrivSqZeroExt ℂ (ℂ × ℂ)) u.left U hUu f).snd := by
    rintro l x hx rfl
    exact (congrArg TrivSqZeroExt.snd (evalPt_spMap_comp (TrivSqZeroExt.map l).toRingHom u.left U hUu hx f)).trans
      (TrivSqZeroExt.snd_map _ _)
  rw [map_add (f := _), ← h.2 U hU1 f, ← h'.2 U hU2 f, key _ _ hU h3, key _ _ hU1 h1, key _ _ hU2 h2]
  rfl

end Deriv

end GlobalTheory.PointUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem eq_one_of_surjective_appTop_of_section {X S : Scheme.{0}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
    (hs : Function.Surjective p.appTop.hom) (a : Γ(X, ⊤)) (ha : o.appTop.hom a = 1) : a = 1 := by
  obtain ⟨b, rfl⟩ := hs a
  have e : o.appTop.hom (p.appTop.hom b) = b := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ho, Scheme.Hom.id_appTop]
    rfl
  rw [e.symm.trans ha, map_one]

theorem exists_sabMap_of_isProper_of_lbIso : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → LBIso t'.PP.L (t.PP.L.pull φ) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hG E _ _ _ H S S' t t' f φ hp gp ⟨w, hw⟩ hact
  obtain ⟨w', hw', Hr⟩ := TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G)
    (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback gp.1 hp
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have hA₃ := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
  refine ⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr,
    TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩
  let o := lift (1 : 𝟙_ (Over S') ⟶ t'.G) (lift (1 : 𝟙_ (Over S') ⟶ t'.G) (1 : 𝟙_ (Over S') ⟶ t'.G))
  have h₁ : pullU o.left ⊤ a = 1 := unit_ext fun y _ =>
    (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans
      ((ha y).trans (map_one _).symm))
  exact Units.ext (eq_one_of_surjective_appTop_of_section (G3 t'.G).hom o.left (Over.w o) (hG _ _ hA₃).2 a.val
    (congrArg Units.val h₁))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {g : ℕ}

def ReadsPeriods (t : SAB H S) {T : Over S} (c₀ : ℂˣ → Γ(T.left, ⊤)ˣ) (D : Datum H) (ty : Fin g → (E →+* ℂ))
    (P : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (T ⟶ t.G)) : Prop :=
  (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧
    ∀ (k : ℕ) (a a₂ : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a a₂ : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (c₀ c)

theorem int_eq_of_exp_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  have hk : 0 < (n - m).natAbs + 1 := Nat.succ_pos _
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  have h0 : (((n - m).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ((n - m : ℤ) : ℂ) = ((((n - m).natAbs + 1 : ℕ) : ℤ) * j : ℤ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((n - m).natAbs + 1 : ℕ) : ℂ) = k at h0 hj
    field_simp at hj
    linear_combination (2 * Real.pi * Complex.I) * hj
  have h2 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j, Int.cast_injective h1⟩ (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem discrete_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    DiscreteTopology P.range.toIntSubmodule := hP.2.2.1

theorem countable_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    (P.range : Set (Fin g → ℂ)).Countable :=
  have := hP.2.2.1
  countable_of_isDiscrete_finiteDimensional DiscreteTopology.isDiscrete

theorem exists_linearEquiv_of_period {t : SAB H S} {y : Sp ℂ ⟶ S} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {g₀ : ℕ} {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ t.G)}
    (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t.semi.separated
  have := discrete_periods hP
  have : IsZLattice ℝ P.range.toIntSubmodule := ⟨hP.2.2.2.1⟩
  exact he.exists_linearEquiv P.range.toIntSubmodule hk ha hs hh hc

theorem exists_isometry {t : SAB H S} {y : Sp ℂ ⟶ S} {D D' : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P')
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e) (he' : IsExp e')
    (hr : ReadsPeriods t unitOn D ty P e) (hr' : ReadsPeriods t unitOn D' ty P' e') :
    ∃ (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ ∀ z, e' (h z) = e z := by
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' he' hr'.1 he.1 he.2.1 he.2.2.1
    ((countable_periods hP).mono fun z hz => (hr.1 z).1 hz)
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (hr'.1 _).1 ((eq_iff_sub_of_add he'.1 _ _).1
          (((hh _).trans (hr.2.1 a x)).trans (by rw [← hh]; exact (hr'.2.1 a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a => (hr'.1 _).1 ((hh _).trans ((hr.1 _).2 ⟨a, rfl⟩))
  choose r₀ hr₀ using hmem
  let r₁ : D.La →ₗ[𝓞 E] D'.La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add (f := _), hr₀, hr₀, hr₀, map_add (f := _), map_add (f := _)])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  have hb : Function.Bijective r₁ := by
    refine ⟨fun a b hab => hP.2.1 (h.injective (((hr₀ a).symm.trans (congrArg P' hab)).trans (hr₀ b))), fun b => ?_⟩
    obtain ⟨a, ha⟩ := (hr.1 (h.symm (P' b))).1 (by rw [← hh, h.apply_symm_apply]; exact (hr'.1 _).2 ⟨b, rfl⟩)
    exact ⟨a, hP'.2.1 ((hr₀ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective r₁ hb, h, fun a b => int_eq_of_exp_eq fun k hk => ?_, hr₀, hh⟩
  have w := hr.2.2 k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have w' := hr'.2.2 k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh] at w'
  exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ y k _ _ _ _ w' w)

theorem div_eq_iff {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)} (hP : Function.Injective P)
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n)
    (a b : L) : e ((n : ℂ)⁻¹ • P a) = e ((n : ℂ)⁻¹ • P b) ↔ ∃ x, a = b + n • x := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [eq_iff_sub_of_add he, hk, ← smul_sub, ← map_sub]
  refine exists_congr fun x => ?_
  rw [eq_inv_smul_iff₀ h0, Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.eq_iff, eq_sub_iff_add_eq', eq_comm]

theorem exists_div_of_pow {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)}
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n) {x : Q} (hx : x ^ n = 1) :
    ∃ a, x = e ((n : ℂ)⁻¹ • P a) := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨z, rfl⟩ := hs x
  have hp : ∀ m : ℕ, e (m • z) = e z ^ m := fun m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, map_zero_of_add he]
    | succ m ih => rw [succ_nsmul, he, ih, pow_succ]
  obtain ⟨a, ha⟩ := (hk _).1 ((hp n).trans hx)
  exact ⟨a, by rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h0]⟩

theorem exists_pointEquiv {S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {y : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G y φ) :
    ∃ β : (𝟙_ (Over S') ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (β x).left = x.left ≫ φ := by
  have w : ∀ x : 𝟙_ (Over S') ⟶ G', x.left ≫ G'.hom = 𝟙 S' := fun x => Over.w x
  let f : (𝟙_ (Over S') ⟶ G') → (Over.mk y ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = y
    rw [Category.assoc, h.1.w, ← Category.assoc, w]
    exact Category.id_comp y)
  have hb : Function.Bijective f := by
    refine ⟨fun a b hab => Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((w a).trans (w b).symm)),
      fun x => ?_⟩
    have hx : x.left ≫ G.hom = 𝟙 S' ≫ y := (Over.w x).trans (Category.id_comp y).symm
    exact ⟨Over.homMk (h.1.lift x.left (𝟙 S') hx) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ hx)⟩
  refine ⟨⟨Equiv.ofBijective f hb, fun a b => Over.OverMorphism.ext ?_⟩, fun _ => rfl⟩
  exact (h.2 _ a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm.trans
    (mul_left_congr (Category.id_comp y) _ _ _ _ rfl rfl)

theorem weilIs_congr {X : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {a b : X ⟶ S} (h : a = b) {k : ℤ}
    {x y : Over.mk a ⟶ G} {x' y' : Over.mk b ⟶ G} (hx : x.left = x'.left) (hy : y.left = y'.left)
    {c : Γ(X, ⊤)ˣ} (H : Out.WeilIs G L k x y c) : Out.WeilIs G L k x' y' c := by
  subst h
  rwa [← Over.OverMorphism.ext hx, ← Over.OverMorphism.ext hy]

end GlobalTheory.UnifPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropicOfLaws
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem lbPow_descends_of_isotropic_of_laws : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) :=
  LinDescent.lbPow_descends

end GlobalTheory
end
end

