module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldEvalOriginEqTangentDerivativ
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin

variable {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}}

theorem valR_eq_germ (x : Sp A ⟶ X) (U : X.Opens) (hx : x (IsLocalRing.closedPoint A) ∈ U) (f : Γ(X, U)) :
    valR x U f = (X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom f := by
  have e : X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of A) x =
      x.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem x hx).ge ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [e, valR, dite_eq_left (Scheme.preimage_eq_top_of_closedPoint_mem x hx).ge]
  rfl

end GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem eta_hom : (η[G]).left ≫ G.hom = 𝟙 (Sp R) := Over.w (η[G])

theorem isTr_eta_tv (v : TanM (𝟙 (Sp R)) G) :
    IsTr G (RingHom.id R) (η[G]).left v (tv v).left := by
  have hη := eta_hom G
  refine ⟨1, Over.homMk (tv v).left ?_, ?_, ?_, ?_⟩
  · have := Over.w (tv v)
    simp only [Over.mk_hom, Category.comp_id] at this ⊢
    rw [this, hη, Category.comp_id]
  · rw [one_left]
    simp [hη]
  · have hd : dualMap (RingHom.id R) = RingHom.id (DualNumber R) := by
      ext x <;> simp [dualMap]
    simp [hd, spMap]
  · rw [_root_.one_mul]
    rfl

theorem evO_germ_of_isInv (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (O : G.left.Opens)
    (hO : origin G ∈ O) (f : Γ(G.left, O)) :
    evO G ((G.left.presheaf.germ O (origin G) hO).hom (dd O f)) =
      tanDer G v ((G.left.presheaf.germ O (origin G) hO).hom f) := by
  have hη := eta_hom G
  have hg : (η[G]).left ≫ G.hom = spMap (RingHom.id R) := by
    rw [hη]; simp [spMap]
  have hO' : (tv v).left (IsLocalRing.closedPoint (DualNumber R)) ∈ O := by
    rw [tv_closedPoint]; exact hO
  have htop : ⊤ ≤ (η[G]).left ⁻¹ᵁ O := (Scheme.preimage_eq_top_of_closedPoint_mem _ hO).ge
  have key := hinv.2 R (RingHom.id R) (η[G]).left (tv v).left O f hg htop (isTr_eta_tv G v)
  rw [valR_eq_germ _ O hO', valR_eq_germ (η[G]).left O hO] at key
  rw [tanDer_eq, evO]
  have e2 : G.left.presheaf.germ O (origin G) hO ≫
      (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G v).symm)).hom =
        G.left.presheaf.germ O _ hO' := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ _
  rw [← CommRingCat.comp_apply, ← Category.assoc, e2]
  exact key.symm
end GlobalTheory.CoordsOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGenericFibreInjectiveDomainMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isAbelianScheme_generic_of_injective (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (ρ : R →+* R') (hρ : Function.Injective ρ) (G : Over (Sp R)) [GrpObj G]
    (h : IsAbelianScheme ((Over.pullback (jK R)).obj G)) :
    IsAbelianScheme ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) := by
  let ρK : FractionRing R →+* FractionRing R' := IsFractionRing.map (A := R) (B := R') (j := ρ) hρ
  have hc : jK R' ≫ spMap ρ = spMap ρK ≫ jK R := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    simp [ρK, IsFractionRing.map, IsLocalization.map_eq]
  have h2 : IsAbelianScheme ((Over.pullback (spMap ρK)).obj ((Over.pullback (jK R)).obj G)) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ h
  have h3 : IsAbelianScheme ((Over.pullback (spMap ρK ≫ jK R)).obj G) :=
    GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso (pullCompIso (spMap ρK) (jK R) G) inferInstance h2
  rw [← hc] at h3
  exact GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso (pullCompIso (jK R') (spMap ρ) G).symm
    (inferInstanceAs (IsMonHom (pullCompIso (jK R') (spMap ρ) G).inv)) h3

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibres
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.ZM GlobalTheory.AbLaw.CubeGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddFib

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def quad {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) : Fin 4 → (Z.left ⟶ (A ⊗ T).left) :=
  ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left, (lift 1 y).left]

abbrev uquad (A T : Over S) [GrpObj A] : Fin 4 → ((A ⊗ (A ⊗ T)).left ⟶ (A ⊗ T).left) :=
  quad (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

theorem comp_quad {Z Z' : Over S} (r : Z' ⟶ Z) (x x' : Z ⟶ A) (y : Z ⟶ T) (i : Fin 4) :
    r.left ≫ quad x x' y i = quad (r ≫ x) (r ≫ x') (r ≫ y) i := by
  fin_cases i <;>
  · simp only [quad, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    rw [← Over.comp_left, comp_lift]
    try simp only [MonObj.comp_mul, MonObj.comp_one]

theorem prod_quad {Z : Over S} {x x' : Z ⟶ A} (y : Z ⟶ T) (h : x = 1 ∨ x' = 1)
    (U : Type) [CommGroup U] (k : (Z.left ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (quad x x' y i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  rcases h with rfl | rfl
  · simp [Fin.prod_univ_four, quad, -Over.comp_left]
  · simp [Fin.prod_univ_four, quad, -Over.comp_left, mul_comm]

theorem homMk_comp_eq_one {Y : Over S} {Z : Scheme.{0}} (r : Z ⟶ Y.left) (u : Y ⟶ A) (b : Z ⟶ S)
    (h : r ≫ u.left = b ≫ η[A].left) : (Over.homMk r rfl : Over.mk (r ≫ Y.hom) ⟶ Y) ≫ u = 1 := by
  have hb : b = r ≫ Y.hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  apply Over.OverMorphism.ext
  rw [Hom.one_def]
  exact h.trans (by rw [hb]; rfl)

theorem formal_quad {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ (A ⊗ T)).left) (b : Z ⟶ S)
    (h : r ≫ (fst A (A ⊗ T)).left = b ≫ η[A].left ∨ r ≫ (snd A (A ⊗ T) ≫ fst A T).left = b ≫ η[A].left)
    (U : Type) [CommGroup U] (k : (Z ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (r ≫ uquad A T i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  have e : ∀ i, r ≫ uquad A T i = quad ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ fst A (A ⊗ T))
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ fst A T)
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ snd A T) i :=
    fun i ↦ comp_quad (Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) _ _ _ i
  simp only [e]
  exact prod_quad _ (h.imp (homMk_comp_eq_one r _ b) (homMk_comp_eq_one r _ b)) U k

theorem triv_quad_iff {N : LB (A ⊗ T).left} (hN : N.IsLB) {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) :
    Triv (LB.LinComb N (quad x x' y) ![1, -1, -1, 1]) ↔
      evc hN (x * x') y - evc hN x y - evc hN x' y + evc hN 1 y = 0 := by
  refine (cls_eq_zero_iff (LB.isLB_linComb hN _ _)).symm.trans ?_
  rw [cls_linComb hN, Fin.sum_univ_four]
  have e : ∀ a b c d : Pic Z.left, (1 : ℤ) • a + (-1 : ℤ) • b + (-1 : ℤ) • c + (1 : ℤ) • d = a - b - c + d :=
    fun a b c d ↦ by simp only [one_smul, neg_smul]; abel
  simp only [quad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
  rw [e]
  rfl


omit [GrpObj A] in
theorem exists_chart {X : Scheme.{0}} (j : X ⟶ T.left) :
    ∃ q : ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).left ⟶ (A ⊗ (A ⊗ T)).left,
      IsPullback q ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).hom
        (snd A (A ⊗ T) ≫ snd A T).left j ∧
      q ≫ (fst A (A ⊗ T)).left =
        (fst _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T) ≫ fst A T).left =
        (snd _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) := by
  set B := (Over.pullback (j ≫ T.hom)).obj A
  have hB : IsPullback (pullback.fst A.hom (j ≫ T.hom)) B.hom A.hom (j ≫ T.hom) := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback _ _
  have h3 : IsPullback (fst A (A ⊗ T)).left (snd A (A ⊗ T)).left A.hom (A ⊗ T).hom := IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  obtain ⟨m, m₁, m₂⟩ : ∃ m : B.left ⟶ (A ⊗ T).left, m ≫ (fst A T).left = pullback.fst A.hom (j ≫ T.hom) ∧
      m ≫ (snd A T).left = B.hom ≫ j :=
    ⟨h2.lift _ _ (by rw [hB.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m B.hom (snd A T).left j := IsPullback.of_right (by rw [m₁]; exact hB) m₂ h2
  have mw : m ≫ (A ⊗ T).hom = B.hom ≫ j ≫ T.hom := by
    rw [← Over.w (snd A T), ← Category.assoc, m₂, Category.assoc]
  have ho : IsPullback ((fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom)) (snd B B).left A.hom
      (m ≫ (A ⊗ T).hom) := by
    rw [mw]; exact hBB.paste_horiz hB
  obtain ⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ B).left ⟶ (A ⊗ (A ⊗ T)).left,
      q ≫ (fst A (A ⊗ T)).left = (fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T)).left = (snd B B).left ≫ m :=
    ⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩
  have hq : IsPullback q (snd B B).left (snd A (A ⊗ T)).left m :=
    IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3
  refine ⟨q, ?_, q₁, ?_⟩
  · rw [← Over.w (snd B B)]
    exact hq.paste_vert hm
  · show q ≫ (snd A (A ⊗ T)).left ≫ (fst A T).left = _
    rw [← Category.assoc, q₂, Category.assoc, m₁]

theorem isAdditive_of_geomFibres (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (N : LB (A ⊗ T).left) (hN : N.IsLB) (h0 : Triv (ev N (1 : T ⟶ A) (𝟙 T)))
    (hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ T),
      IsAdditive (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t))) : IsAdditive N := by
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  have := hA.geomConnected
  have := hA.smooth
  have := hA.proper
  have one₁ : ∀ {Z : Over S} (y : Z ⟶ T), evc hN (1 : Z ⟶ A) y = 0 := fun y ↦ by
    have e := congrArg (CechPic.pull y.left) ((triv_ev_iff hN _ _).1 h0)
    rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e
  have H := GlobalTheory.CubeNoeth.fibTriv_clopen N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left
    (fun R _ _ j ↦ by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_chart (A := A) j
    have hB := isAb_baseChange hA (j ≫ T.hom)
    have one := one_left_fst (A := A) (j ≫ T.hom)
    let B := (Over.pullback (j ≫ T.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN' : (LB.LinComb N (fun k ↦ q ≫ uquad A T k) ![1, -1, -1, 1]).IsLB := DVR.linComb_isLB _ hN _ _
    have pf : ∀ M : LB (B ⊗ B).left, M.IsLB → Nonempty (Perf (B ⊗ B).hom M) := fun M hM ↦
      ProperFinite.nonempty_perf_of_isProper (R := R) (B ⊗ B).hom hM
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN' (pf _ hN') (pf _ (isLB_pw hN' _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' ↦ CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN' (pf _ hN') ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inr ?_))
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inl ?_))
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have all : ∀ t, t ∈ fibTriv N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left := fun t ↦ by
    let K := AlgebraicClosure (T.left.residueField t)
    let g : Spec (CommRingCat.of K) ⟶ T.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) ≫ T.left.fromSpecResidueField t
    let s : Sp K ⟶ S := g ≫ T.hom
    let t' : Over.mk s ⟶ T := Over.homMk g rfl
    have hadd := hgeo K s t'
    let π := pullback.fst (snd A (A ⊗ T) ≫ snd A T).left g
    let f' := pullback.snd (snd A (A ⊗ T) ≫ snd A T).left g
    refine ⟨K, inferInstance, g, _, π, f', ⟨IsLocalRing.closedPoint K, ?_⟩, IsPullback.of_hasPullback _ _, ?_⟩
    · have := (Scheme.range_fromSpecResidueField t).le
        ⟨Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) (IsLocalRing.closedPoint K), rfl⟩
      exact this
    let Zs : Over S := Over.mk (f' ≫ s)
    have w : π ≫ (A ⊗ (A ⊗ T)).hom = f' ≫ s := by
      rw [← Over.w (snd A (A ⊗ T) ≫ snd A T), ← Category.assoc, pullback.condition, Category.assoc]
    let x : Zs ⟶ A ⊗ (A ⊗ T) := Over.homMk π w
    let τ : Zs ⟶ Over.mk s := Over.homMk f' rfl
    have hx : x ≫ snd A (A ⊗ T) ≫ snd A T = τ ≫ t' := Over.OverMorphism.ext pullback.condition
    have hM : (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t')).IsLB := pull_isLB hN _
    have ev₁ : ∀ a : Zs ⟶ A, evc hM a τ = evc hN a (x ≫ snd A (A ⊗ T) ≫ snd A T) := fun a ↦ by
      rw [evc_ev hN, lift_fst, lift_snd_assoc, hx]
    have e := (isAdditive_iff hM).1 hadd Zs (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T) τ
    rw [ev₁, ev₁, ev₁] at e
    have ef : (fun k ↦ π ≫ uquad A T k) = quad (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T)
        (x ≫ snd A (A ⊗ T) ≫ snd A T) := funext fun k ↦ comp_quad x _ _ _ k
    unfold TrivAt
    rw [ef, triv_quad_iff hN, one₁, e]
    abel
  let e : T ⟶ A ⊗ (A ⊗ T) := lift 1 (lift 1 (𝟙 T))
  have e₀ : e ≫ fst A (A ⊗ T) = 1 := by simp [e]
  have e₂ : e ≫ snd A (A ⊗ T) ≫ snd A T = 𝟙 _ := by simp [e]
  have htr := triv_of_local hN (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left e.left
    (congrArg (fun q ↦ q.left) e₂) (fun Z b ↦ formal_quad (b ≫ e.left) (b ≫ T.hom) (Or.inl ?_))
    (fun V ↦ ?_) (fun s ↦ H.1 (all s))
  rotate_left
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_chart (A := A) V.ι
    have hB := isAb_baseChange hA (V.ι ≫ T.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2
  refine (isAdditive_iff hN).2 fun Y a a' t ↦ ?_
  have h1 : TrivAt N (uquad A T) ![1, -1, -1, 1] (lift a (lift a' t)).left := by
    have h0' : TrivAt N (uquad A T) ![1, -1, -1, 1] (𝟙 _) := by
      unfold TrivAt; simp only [Category.id_comp]; exact htr
    have := h0'.comp (lift a (lift a' t)).left
    rwa [Category.comp_id] at this
  have ef : (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) = quad a a' t := funext fun k ↦ by
    rw [comp_quad]; simp only [lift_fst, lift_snd_assoc, lift_snd]
  have h2 : Triv (LB.LinComb N (quad a a' t) ![1, -1, -1, 1]) := by
    have h1' : Triv (LB.LinComb N (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) ![1, -1, -1, 1]) := h1
    rwa [ef] at h1'
  have h3 := (triv_quad_iff hN a a' t).1 h2
  rw [one₁, add_zero, sub_sub, sub_eq_zero] at h3
  exact h3

end GlobalTheory.AddFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageTranslatesSeparatedGrp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TransAff

theorem comp_mul_hom {R' : Type} [CommRing R'] {G' T T' : Over (Sp R')} [GrpObj G'] (x : T' ⟶ T) (f g : T ⟶ G') :
    x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem comp_one_hom {R' : Type} [CommRing R'] {G' T T' : Over (Sp R')} [GrpObj G'] (x : T' ⟶ T) :
    x ≫ (1 : T ⟶ G') = 1 := by
  simp [Hom.one_def]

theorem comp_inv_eq (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G']
    (a : 𝟙_ (Over (Sp R')) ⟶ G') (b : 𝟙_ (Over (Sp R')) ⟶ G') (hab : a * b = 1) :
    (𝟙 G' * (toUnit G' ≫ a)) ≫ (𝟙 G' * (toUnit G' ≫ b)) = 𝟙 G' := by
  rw [comp_mul_hom, Category.comp_id, ← Category.assoc, toUnit_unique (_ ≫ toUnit G') (toUnit G'),
    _root_.mul_assoc, ← comp_mul_hom, hab, comp_one_hom, _root_.mul_one]

theorem isAffineOpen_translates :
    ∀ (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSeparated G'.hom → ∀ (a : 𝟙_ (Over (Sp R')) ⟶ G') (W : G'.left.Opens), IsAffineOpen W → IsAffineOpen ((𝟙 G' * (toUnit G' ≫ a)).left ⁻¹ᵁ W ⊓ (𝟙 G' * (toUnit G' ≫ a⁻¹)).left ⁻¹ᵁ W) := by
  intro R' _ G' _ hs a W hW
  have e1 := comp_inv_eq R' G' a a⁻¹ (mul_inv_cancel a)
  have e2 := comp_inv_eq R' G' a⁻¹ a (inv_mul_cancel a)
  have i1 : IsIso (𝟙 G' * (toUnit G' ≫ a)).left :=
    ⟨⟨(𝟙 G' * (toUnit G' ≫ a⁻¹)).left, by rw [← Over.comp_left, e1]; rfl,
      by rw [← Over.comp_left, e2]; rfl⟩⟩
  have i2 : IsIso (𝟙 G' * (toUnit G' ≫ a⁻¹)).left :=
    ⟨⟨(𝟙 G' * (toUnit G' ≫ a)).left, by rw [← Over.comp_left, e2]; rfl,
      by rw [← Over.comp_left, e1]; rfl⟩⟩
  have : IsSeparated G'.hom := hs
  have : G'.left.IsSeparated := ⟨by rw [← terminal.comp_from G'.hom]; infer_instance⟩
  exact (hW.preimage_of_isIso _).inf (hW.preimage_of_isIso _)

end GlobalTheory.TransAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfLbPowLbIsoLinComb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.AmplePowLinComb

open GlobalTheory.CechPic

def genClasses (X : Scheme.{0}) : AddSubmonoid (Pic X) where
  carrier := {c | ∃ (A : LB X) (hA : A.IsLB), IsGenerated A ∧ cls A hA = c}
  zero_mem' := ⟨_, LB.isLB_triv X, isGenerated_triv X, rfl⟩
  add_mem' := by
    rintro _ _ ⟨A, hA, gA, rfl⟩ ⟨B, hB, gB, rfl⟩
    exact ⟨tens A B, isLB_tens hA hB, AmpleModelPos.isGenerated_tens gA gB, cls_tens hA hB _⟩

theorem isAmpleLB_of_lbPow_lbIso_linComb : ∀ (X : Scheme.{0}) (L M : LB X), IsAmpleLB M → L.IsLB →
    ∀ (N a₀ r : ℕ) (a : Fin r → ℕ) (β : Fin r → (X ⟶ X)), 1 ≤ N → 1 ≤ a₀ →
    LBIso (lbPow L N) (LB.LinComb M (K := Option (Fin r)) (fun o => o.elim (𝟙 X) fun i => β i)
      fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) → IsAmpleLB L := by
  intro X L M hM hL N a₀ r a β hN ha₀ H
  obtain ⟨k, hk, gk⟩ := hM.exists_isGenerated_pow
  have hMk := isLB_lbPow hM.isLB k

  set c : Pic X := ∑ i, a i • pull (β i) (cls _ hMk) with hc
  have hcmem : c ∈ genClasses X := by
    refine AddSubmonoid.sum_mem _ fun i _ => AddSubmonoid.nsmul_mem _ ?_ _
    exact ⟨_, pull_isLB hMk (β i), gk.pull (β i), cls_pull hMk (β i) _⟩
  obtain ⟨A, hA, gA, hAc⟩ := hcmem
  have hLN := isLB_lbPow hL (N * k)
  have hMa := isLB_lbPow hM.isLB (a₀ * k)
  have hAmp : IsAmpleLB (lbPow M (a₀ * k)) :=
    (isAmpleLB_pow_iff hM.isLB (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).2 hM
  have h₁ := LB.isLB_div hLN hMa
  have h₂ := LB.isLB_div h₁ hA
  have hLpow : IsAmpleLB (lbPow L (N * k)) := hAmp.tensor_isGenerated gA hLN ((cls_eq_zero_iff h₂).1 ?_)
  · exact (isAmpleLB_pow_iff hL (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).1 hLpow
  have hE := (cls_eq_iff (isLB_lbPow hL N) (LB.isLB_linComb hM.isLB _ _)).2 H
  rw [cls_lbPow hL, cls_linComb hM.isLB, Fintype.sum_option] at hE
  rw [cls_div h₁ hA, cls_div hLN hMa, hAc, hc, cls_lbPow hL, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  simp only [Option.elim, pull_id] at hE
  simp only [map_nsmul]
  have e1 : (N * k) • cls L hL = k • (N • cls L hL) := by rw [smul_smul, mul_comm]
  rw [e1, hE]
  simp only [natCast_zsmul, smul_add, Finset.smul_sum, smul_smul]
  rw [sub_sub, sub_eq_zero, mul_comm a₀ k]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

end GlobalTheory.AmplePowLinComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFiniteBase

theorem isAmpleLB_of_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ∀ (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) π → ∀ L : LB G.left, L.IsLB → IsAmpleLB (L.pull π) → IsAmpleLB L := by
  intro R R' _ _ _ _ _ _ _ _ _ _ ρ hinj hfin G _ G' _ π hG h L hL hA
  have := hG.smooth
  have := hG.quasiCompact
  have hF : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hfin
  have hS : Surjective (spMap ρ) := ⟨hfin.to_isIntegral.comap_surjective hinj⟩
  have : IsFinite π := MorphismProperty.of_isPullback (P := @IsFinite) h.1.flip hF
  have hs : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip hS
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hN : GlobalTheory.IsNormalScheme G.left := isNormalScheme_of_smooth G.hom
  exact GlobalTheory.NormalDescent.isAmpleLB_of_pull G.left G'.left π ⟨⟩
    (fun x => ⟨hN.1 x, hN.2 x⟩) inferInstance hs.surj L hL hA

end GlobalTheory.AmpleFiniteBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective : ∀ (F : Type) [Field F] [NumberField F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F) (L : LB X) (hL : L.IsLB) (L' : LB Y) (hL' : L'.IsLB), π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → CechPic.pull π (cls L hL) = cls L' hL' → (letI := algebraΓOfHom p; IsNef F L') → (letI := algebraΓOfHom sX; IsNef F L) := by
  first | exact @GlobalTheory.NefDescent.isNef_of_pull | exact GlobalTheory.NefDescent.isNef_of_pull | (intros; apply GlobalTheory.NefDescent.isNef_of_pull <;> assumption)
end

