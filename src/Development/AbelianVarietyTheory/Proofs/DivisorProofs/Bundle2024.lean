module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoPreservesRigidificationAtOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.normW_origin : ∀ (V : Type) [CommRing V] [IsDomain V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (A : Over (Sp (FractionRing V))) [GrpObj A] [IsCommMonObj A] (θ : (Over.pullback (jK V)).obj G ⟶ A) [IsMonHom θ]
    (φ : A.left ⟶ G.left), θ.left ≫ φ = pullback.fst G.hom (jK V) →
    ∀ (he : eSec A ≫ φ = spMap (algebraMap V (FractionRing V)) ≫ eSec G)
    (LP : LB A.left) (LL LM : LB G.left), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (rA : LB.Gen (LP.pull (eSec A))) (rL : LB.Gen (LL.pull (eSec G))) (rM : LB.Gen (LM.pull (eSec G)))
      (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ.left) (LM.pull (pullback.fst G.hom (jK V)))),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK V)).obj G).left) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        pullback.fst G.hom (jK V) (r z) ∈ LL.U i → pullback.fst G.hom (jK V) (r z) ∈ LM.U j → θ.left (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) =
          (gm (r ≫ pullback.fst G.hom (jK V)) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ.left) z i k) →
      LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) rA
        (rigPullOf φ (spMap (algebraMap V (FractionRing V))) he LL rL) →
      LB.Gen.Maps (LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)) rM rL →
      ∀ (z : Sp (FractionRing V)) (JA : (Sp (FractionRing V) ⟶ A.left) → LP.ι) (JG : (Sp (FractionRing V) ⟶ G.left) → LM.ι),
        Good LP z JA → Good LM z JG →
        gw w₀ (eSec ((Over.pullback (jK V)).obj G)) z (JG (jK V ≫ eSec G)) (fun _ => JA (eSec A)) *
            val (L := LP) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rA (𝟙 _) z JA =
          val (L := LM) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) rM (jK V) z JG := by
  intro V _ _ G _ _ A _ _ θ _ φ hφ he LP LL LM hP hL hM rA rL rM ψ e w₀ hpt hψ hε z JA JG gA gG
  have h1 : eSec ((Over.pullback (jK V)).obj G) ≫ θ.left = eSec A := by
    show η[(Over.pullback (jK V)).obj G].left ≫ θ.left = η[A].left
    rw [← Over.comp_left, IsMonHom.one_hom]
  have h2 : eSec ((Over.pullback (jK V)).obj G) ≫ pullback.fst G.hom (jK V) = jK V ≫ eSec G := by
    rw [← hφ, ← Category.assoc, h1, he]
  have p1 : θ.left (eSec ((Over.pullback (jK V)).obj G) z) = eSec A z := congrArg (fun f => f z) h1
  have p2 : pullback.fst G.hom (jK V) (eSec ((Over.pullback (jK V)).obj G) z) = eSec G (jK V z) :=
    congrArg (fun f => f z) h2
  have p3 : φ (eSec A z) = eSec G (jK V z) := congrArg (fun f => f z) he
  have hA : eSec A z ∈ LP.U (JA (eSec A)) := gA (eSec A)
  have hG : eSec G (jK V z) ∈ LM.U (JG (jK V ≫ eSec G)) := gG (jK V ≫ eSec G)
  obtain ⟨i, hi⟩ := exists_chart hL (eSec G (jK V z))

  have s2 := hpt _ (eSec ((Over.pullback (jK V)).obj G)) z i (JG (jK V ≫ eSec G)) (JA (eSec A))
    (by rw [p2]; exact hi) (by rw [p2]; exact hG) (by rw [p1]; exact hA)
  rw [h2, h1] at s2

  have s3 := (maps_iff ψ (fun _ : PUnit => eSec A) (fun _ => eSec G) (fun _ => 1) rA rL
    (spMap (algebraMap V (FractionRing V))) _ (rigPull_le φ _ he LL) (fun _ => rfl)).1 hψ
    _ (𝟙 _) z (fun _ => i) (fun _ => JA (eSec A))
    (fun _ => by show φ (eSec A z) ∈ _; rw [p3]; exact hi) (fun _ => hA)
  simp only [Category.id_comp, Fintype.prod_unique, zpow_one] at s3

  have hm : jK V z ∈ (LB.wchart LL (fun _ : PUnit => eSec G) (fun _ => i) ⊓
      LB.wchart LM (fun _ : PUnit => eSec G) (fun _ => JG (jK V ≫ eSec G)) : (Sp V).Opens) := by
    exact ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hG⟩
  have s4 := congrArg (gm (jK V) z _) (hε (fun _ => i, fun _ => JG (jK V ≫ eSec G)))
  have eU : gm (jK V) z _ ((LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s
      (fun _ => i, fun _ => JG (jK V ≫ eSec G))) =
      gm (jK V ≫ eSec G) z (LL.U i ⊓ LM.U (JG (jK V ≫ eSec G))) (e.s (i, JG (jK V ≫ eSec G))) := by
    show gm _ z _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (e.s (i, JG (jK V ≫ eSec G))))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z _ hm _).trans (gm_pull _ _ z _ (show eSec G (jK V z) ∈ LL.U i ⊓ LM.U (JG (jK V ≫ eSec G)) from ⟨hi, hG⟩) _)
  have s4' := (gm_res _ z _ hm _).symm.trans (s4.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) eU (gm_res _ z _ hm _))))
  rw [val_of rA (𝟙 _) z JA (fun _ => JA (eSec A)) (fun _ => by rw [Category.id_comp]),
    val_of rM (jK V) z JG (fun _ => JG (jK V ≫ eSec G)) (fun _ => rfl), s2, _root_.mul_assoc, ← s3]
  exact inv_mul_eq_of_eq_mul s4'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingComplexEmbeddedFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_complexEmbeddedField : GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → ∀ (F : Type) [Field F], Nonempty (F →+* ℂ) → ∀ (X : Scheme.{0}) (p : X ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef F N) → (letI := algebraΓOfHom p; IsBig F N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  first | exact @GlobalTheory.VanishEmbedded.subsingleton_coh_canon_tens | exact GlobalTheory.VanishEmbedded.subsingleton_coh_canon_tens | (intros; apply GlobalTheory.VanishEmbedded.subsingleton_coh_canon_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kernel_finiteFlat_subgroup : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∃ (H : Over (Sp R)) (_ : GrpObj H)
    (i : H ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Flat H.hom ∧
    ∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  intro R _ _ A _ hA L hL ha
  obtain ⟨Z, i, hci, hfin, hflat, hZ⟩ := GlobalTheory.kernelFiniteFlat_holds R A hA L hL ha
  haveI : IsClosedImmersion i.left := hci
  have hmono : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have hmem : ∀ (T : Over (Sp R)) (z : T ⟶ Z), GlobalTheory.MemKL A L (z ≫ i) := fun T z => (hZ T _).2 ⟨z, rfl⟩
  have e1 : (1 : 𝟙_ (Over (Sp R)) ⟶ A) = η[A] := by
    show toUnit _ ≫ η[A] = η[A]
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨o, ho⟩ := (hZ _ η[A]).1 (e1 ▸ memKL_one hL _)
  have e2 : (i ⊗ₘ i) ≫ μ[A] = (fst Z Z ≫ i) * (snd Z Z ≫ i) := by
    show (i ⊗ₘ i) ≫ μ[A] = lift (fst Z Z ≫ i) (snd Z Z ≫ i) ≫ μ[A]
    rw [lift_fst_comp_snd_comp]
  obtain ⟨m, hm⟩ := (hZ _ ((i ⊗ₘ i) ≫ μ[A])).1 (e2 ▸ GlobalTheory.UU.InK.mul hL (hmem _ _) (hmem _ _))
  have e3 : i ≫ GrpObj.inv = (𝟙 Z ≫ i)⁻¹ := by
    rw [Category.id_comp]; rfl
  obtain ⟨n, hn⟩ := (hZ _ (i ≫ GrpObj.inv)).1 (e3 ▸ GlobalTheory.UU.InK.inv hL (hmem _ _))
  obtain ⟨G, hG⟩ := GlobalTheory.exists_grpObj_of_mono i o m n ho hm hn
  exact ⟨Z, G, i, hG, hmono, hfin, hflat, hZ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleRationalPointsFiniteClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KLFinite

theorem finite_of_isFinite {K : Type} [Field K] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of K)) [IsFinite f] :
    Finite Z := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  letI : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hmod : Module.Finite K Γ(Z, ⊤) := by
    show ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.Finite
    rw [CommRingCat.hom_comp]
    exact f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite K _
  have : Finite (Spec (.of Γ(Z, ⊤))) := inferInstanceAs (Finite (PrimeSpectrum _))
  exact Finite.of_injective _ Z.isoSpec.hom.isOpenEmbedding.injective

theorem memKL_of_lam_eq_zero {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) (x : 𝟙_ _ ⟶ A) (h : lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0) : MemKL A L x := by
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  have e := congrArg (CechPic.pull (snd (𝟙_ _) A).left) h
  rw [pull_lam, map_zero, Category.comp_id, ← Category.assoc, comp_toUnit, GlobalTheory.PrimitiveOverField.lam_const,
    toUnit_unique (toUnit _) (fst (𝟙_ _) A)] at e
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ e)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

theorem isClosed_point {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [IsSeparated A.hom]
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) : IsClosed ({x.left (IsLocalRing.closedPoint K)} : Set A.left) := by
  have hx : x.left ≫ A.hom = 𝟙 _ := Over.w x
  have : IsClosedImmersion (x.left ≫ A.hom) := by rw [hx]; infer_instance
  have : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left A.hom
  have h := x.left.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
    (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
      Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
  exact (congrArg IsClosed Set.image_singleton).mp h

end GlobalTheory.KLFinite

theorem GlobalTheory.KLFinite.kl_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ S : Finset A.left, (∀ s ∈ S, IsClosed ({s} : Set A.left)) ∧ ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, GlobalTheory.CechPic.lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0 → x.left (IsLocalRing.closedPoint K) ∈ S := by
  intro K _ _ A _ hA L hL ha
  obtain ⟨Z, i, -, hfin, -, hZ⟩ := GlobalTheory.kernelFiniteFlat_holds K A hA L hL ha
  have : Finite Z.left := GlobalTheory.KLFinite.finite_of_isFinite Z.hom
  have : IsProper A.hom := hA.proper
  have hr : (Set.range i.left).Finite := Set.finite_range _
  classical
  refine ⟨hr.toFinset.filter (fun s => IsClosed ({s} : Set A.left)), fun s hs => (Finset.mem_filter.1 hs).2,
    fun x hx => ?_⟩
  obtain ⟨z, hz⟩ := (hZ _ x).1 (GlobalTheory.KLFinite.memKL_of_lam_eq_zero hL x hx)
  refine Finset.mem_filter.2 ⟨hr.mem_toFinset.2 ⟨z.left (IsLocalRing.closedPoint K), ?_⟩,
    GlobalTheory.KLFinite.isClosed_point x⟩
  rw [← hz, Over.comp_left]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem spMap_comp' {A B K : Type} [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) :
    spMap (h.comp f) = spMap h ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eSec_hom' {S : Scheme.{0}} (G : Over S) [GrpObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  simpa [eSec] using Over.w η[G]

theorem gs_appLE' {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (r : Z ⟶ Y) (p : Z) (U : X.Opens) (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (hp : r p ∈ V) (a : Γ(X, U)) : gs r p V ((φ.appLE U V e).hom a) = gs (r ≫ φ) p U a := by
  rw [← gs_pull r φ p U (e hp) a, ← gs_res r p e hp]
  rfl

theorem dualMap_alg {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) (a : B) :
    GlobalTheory.MBLow.dualMap h (algebraMap B _ a) = algebraMap K _ (h a) := by
  ext <;> simp [GlobalTheory.MBLow.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) :
    GlobalTheory.MBLow.dualMap h DualNumber.eps = DualNumber.eps := by
  ext <;> simp [GlobalTheory.MBLow.dualMap]

theorem dual_decomp {A : Type} [CommRing A] (z : DualNumber A) :
    z = algebraMap A _ z.fst + algebraMap A _ z.snd * DualNumber.eps := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ringHom_dual_ext {A K : Type} [CommRing A] [CommRing K] (F G : DualNumber A →+* K)
    (h1 : ∀ a, F (algebraMap A _ a) = G (algebraMap A _ a)) (h2 : F DualNumber.eps = G DualNumber.eps) : F = G := by
  refine DFunLike.ext _ _ fun z => ?_
  rw [dual_decomp z, map_add (f := _), map_add (f := _), map_mul, map_mul, h1, h1, h2]

end GlobalTheory.KeyEven

namespace GlobalTheory.KeyEven

theorem keyPB_of_keyOn_comp : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K)
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G))
    (x : KeyIn B) (x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g),
    KeyOn f x G L σ (fun i => y (i.cast hg)) → KeyOn (h.comp f) x' G L σ (fun i => y (i.cast hg')) → KeyPB x' x h := by
  intro A B K _ _ _ f h G _ _ L σ g y x x' hg hg' H H'
  obtain ⟨φ, he, ψ, F, hpb, hψ, hrig, hsec, hF1, hF2, hv⟩ := H
  obtain ⟨φ', he', ψ', F', hpb', hψ', hrig', hsec', hF1', hF2', hv'⟩ := H'
  have hc : spMap (h.comp f) = spMap h ≫ spMap f := spMap_comp' f h
  obtain ⟨φ₁, h1, h2⟩ : ∃ φ₁ : x'.P.A.left ⟶ x.P.A.left, φ₁ ≫ φ = φ' ∧ φ₁ ≫ x.P.A.hom = x'.P.A.hom ≫ spMap h :=
    ⟨hpb.1.lift φ' (x'.P.A.hom ≫ spMap h) (by rw [hpb'.1.w, hc, Category.assoc]), hpb.1.lift_fst _ _ _,
      hpb.1.lift_snd _ _ _⟩
  subst h1
  have gp : IsGrpPullback x'.P.A x.P.A (spMap h) φ₁ := IsGrpPullback.cancel hpb (hpb'.congr hc rfl) h2
  have he₁ : eSec x'.P.A ≫ φ₁ = spMap h ≫ eSec x.P.A := by
    apply hpb.1.hom_ext
    · rw [Category.assoc, he', Category.assoc, he, hc, Category.assoc]
    · rw [Category.assoc, h2, ← Category.assoc, eSec_hom', Category.assoc, eSec_hom']
      rfl
  have hL := L.isLB
  have hx := x.P.isLB
  have hx' := x'.P.isLB
  have pψ := (isGen_iff ψ).1 hψ
  have pψ' := (isGen_iff ψ').1 hψ'
  obtain ⟨w, T⟩ := exists_cancel hL ψ ψ' pψ pψ' hx hx'
  have hg₁ : x'.P.g = x.P.g := hg'.trans hg.symm
  refine ⟨φ₁, he₁, w, hg₁, GlobalTheory.MBLow.dualMap h, gp, (isGen_iff w).2 (T.pgen_cancel hL pψ pψ'), ?_, ?_,
    dualMap_alg h, dualMap_eps h, ?_⟩
  ·
    have H := (maps_iff ψ _ (fun _ => eSec G) _ x.rig L.rig (spMap f) _ (rigPull_le φ (spMap f) he L.L)
      (fun _ => rfl)).1 hrig
    have H'' := (maps_iff ψ' _ (fun _ => eSec G) _ x'.rig L.rig (spMap (h.comp f)) _
      (rigPull_le (φ₁ ≫ φ) (spMap (h.comp f)) he' L.L) (fun _ => rfl)).1 hrig'
    rw [hc] at H''
    exact (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap h) _ (rigPull_le φ₁ (spMap h) he₁ x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel hL (fun _ => he₁) H H'')
  ·
    intro j i hle
    apply fn_ext
    intro p hp
    obtain ⟨c, hcp⟩ := exists_chart hL (φ (φ₁ p))
    have hk : φ₁ p ∈ x.P.L.U (j PUnit.unit) := hle hp
    have le₀ : (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) ≤ φ ⁻¹ᵁ L.L.U c := fun q hq => mem_pull.1 hq.1
    have m₀ : φ₁ p ∈ (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) := ⟨mem_pull.2 hcp, hk⟩
    have e₀ := congrArg (gs φ₁ p _) (hsec (fun _ => c) (j PUnit.unit) le₀)
    dsimp only at e₀
    rw [gs_appLE' φ φ₁ p _ _ le₀ m₀] at e₀
    erw [gs_mul φ₁ p _ m₀] at e₀
    erw [gs_unit φ₁ p _ m₀, gs_res φ₁ p _ m₀] at e₀
    have le₁ : ((L.L.pull (φ₁ ≫ φ)).U (fun _ => c)) ⊓ x'.P.L.U i ≤ (φ₁ ≫ φ) ⁻¹ᵁ L.L.U c :=
      fun q hq => mem_pull.1 hq.1
    have m₁ : (𝟙 x'.P.A.left) p ∈ (L.L.pull (φ₁ ≫ φ)).U (fun _ => c) ⊓ x'.P.L.U i := ⟨mem_pull.2 hcp, hp.2⟩
    have e₁ := congrArg (gs (𝟙 _) p _) (hsec' (fun _ => c) i le₁)
    dsimp only at e₁
    rw [gs_appLE' (φ₁ ≫ φ) (𝟙 _) p _ _ le₁ m₁] at e₁
    erw [gs_mul (𝟙 _) p _ m₁] at e₁
    erw [gs_unit (𝟙 _) p _ m₁, gs_res (𝟙 _) p _ m₁] at e₁
    rw [Category.id_comp] at e₁
    have tri := T (x'.P.A.left) (𝟙 _) p c (j PUnit.unit) i hcp hk hp.2
    rw [gs_appLE' φ₁ (𝟙 _) p _ _ hle hp, Category.id_comp]
    erw [gs_mul (𝟙 _) p _ hp]
    erw [gs_unit (𝟙 _) p _ hp, gs_res (𝟙 _) p _ hp]
    change gs φ₁ p _ _ = (gw w (𝟙 _) p (j PUnit.unit) i).val * _
    have e₂ : (gw ψ' (𝟙 _) p c i).val * gs (𝟙 _) p (x'.P.L.U i) (x'.th.f i) =
        (gw ψ φ₁ p c (j PUnit.unit)).val * gs φ₁ p (x.P.L.U (j PUnit.unit)) (x.th.f (j PUnit.unit)) :=
      e₁.symm.trans e₀
    rw [tri, Category.id_comp, Units.val_mul, _root_.mul_assoc] at e₂
    exact ((Units.mul_right_inj _).1 e₂).symm
  ·
    intro i
    apply hpb.1.hom_ext
    · have a1 := hv (i.cast hg₁)
      have a2 := hv' i
      simp only at a1 a2
      rw [Category.assoc, a2, Category.assoc, a1, Fin.cast_cast, ← Category.assoc, ← spMap_comp']
      congr 2
      refine ringHom_dual_ext _ _ (fun a => ?_) ?_
      · simp only [RingHom.comp_apply, hF1, hF1', dualMap_alg]
      · simp only [RingHom.comp_apply, hF2, hF2', dualMap_eps]
    · rw [Category.assoc, h2, ← Category.assoc, Over.w (x'.v i), Category.assoc, Over.w (x.v _)]
      show spMap (algebraMap K (DualNumber K)) ≫ spMap h = spMap (GlobalTheory.MBLow.dualMap h) ≫ spMap (algebraMap B (DualNumber B))
      rw [← spMap_comp', ← spMap_comp']
      congr 1
      exact RingHom.ext fun a => (dualMap_alg h a).symm

end GlobalTheory.KeyEven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSLoc

theorem leibniz_frac {B C : Type} [CommRing B] [CommRing C] (ψ : B →+* C) (d : C → C)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (D : Derivation ℤ B B) {b u r : B} (hu : IsUnit u)
    (h : b * u = r) (h₁ : d (ψ u) = ψ (D u)) (h₂ : d (ψ r) = ψ (D r)) : d (ψ b) = ψ (D b) := by
  subst h
  rw [map_mul, hd, h₁, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul] at h₂
  exact (hu.map ψ).mul_left_cancel (add_left_cancel h₂)

theorem exists_frac {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1))
    (hf : W.1 = X.basicOpen f) (b : Γ(X, W.1)) :
    ∃ u r : Γ(X, U.1), IsUnit ((X.presheaf.map (homOfLE hW).op).hom u) ∧
      b * (X.presheaf.map (homOfLE hW).op).hom u = (X.presheaf.map (homOfLE hW).op).hom r := by
  letI : Algebra Γ(X, U.1) Γ(X, W.1) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
  have hl : IsLocalization.Away f Γ(X, W.1) := U.2.isLocalization_of_eq_basicOpen f (homOfLE hW) hf
  obtain ⟨⟨r, u⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) b
  exact ⟨u.1, r, IsLocalization.map_units Γ(X, W.1) u, h⟩

theorem spMap_res_chart {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE hW).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  U.2.map_fromSpec W.2 (homOfLE hW).op

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem isKS_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (D r)) → GlobalTheory.LogKS.IsKS t V U v D Θ → GlobalTheory.LogKS.IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) DW ((X.presheaf.map (homOfLE hW).op).hom.mapMatrix Θ) := by
  intro E _ _ _ H X t V U W hW f hf n v D DW Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩
  have hWU : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, fun i => Wc i ⊓ t.G.hom ⁻¹ᵁ W.1, j, d, ?_, fun i => inf_le_left.trans (hj i), fun i => ?_,
    fun i h b => ?_, fun i i' O hO g S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [← iSup_inf_eq, hsup, ← Scheme.Hom.preimage_inf, inf_right_comm, inf_eq_right.mpr hW]
  · exact ⟨fun O hO => (hfld i).1 O (hO.trans inf_le_left), fun O hO => (hfld i).2.1 O (hO.trans inf_le_left),
      fun O O' h hO => (hfld i).2.2 O O' h (hO.trans inf_le_left)⟩
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r) =
        resG t.G.left (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i) ((t.G.hom.appLE U.1 (Wc i) (hWU i)).hom r) := by
      intro r
      have e1 := congrArg (fun k => k.hom r) (t.G.hom.map_appLE h (homOfLE hW).op)
      have e2 := congrArg (fun k => k.hom r) (t.G.hom.appLE_map (hWU i)
        (homOfLE (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i)).op)
      exact e1.trans e2.symm
    have key : ∀ r : Γ(X, U.1), d i _ ((t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r)) = (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        (DW ((X.presheaf.map (homOfLE hW).op).hom r)) := by
      intro r
      rw [hD, e, e, (hfld i).2.2 _ _ _ le_rfl, hcomp]
    obtain ⟨u, r, hu, hb⟩ := exists_frac U W hW f hf b
    exact leibniz_frac _ _ ((hfld i).2.1 _ inf_le_left) DW hu hb (key u) (key r)
  · refine htest i i' O (hO.trans (inf_le_inf inf_le_left inf_le_left)) g S
      (φ.comp (X.presheaf.map (homOfLE hW).op).hom) g₀ w ?_ hO' fun a => ?_
    · rw [hg₀, ← spMap_res_chart U W hW, ← Category.assoc, spMap_comp']
    · obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, spMap_comp', dualMap_comp']

end GlobalTheory.LogKSLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerZeroTangentTrivial
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem eq_const_of_isKS_zero : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → IsTanX y x' → IsKS (psiSet H) y x' 0 →
        x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  intro P G E _ _ _ H Dw l Xo c K _ _ y x' hpq hx hks
  obtain ⟨A, _, A', _, π, π', i, h, h1, h2, h3, h4⟩ := _root_.GlobalTheory.KSFull.ksFull P E H Dw l Xo c K y x' hpq hx hks
  obtain ⟨q, hq1, hq2⟩ := _root_.GlobalTheory.FlagTan.exists_retraction_of_ks_zero P G E H Dw l Xo c K y x' hpq hx A A' π π' i h h1 h2 h3 h4
  obtain ⟨o, m⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  have e := Xo.unram K x' o m
    (_root_.GlobalTheory.ConstDeform.objMap_const P G E H Dw l Xo c K y x' hpq hx A A' π π' i q h h1 h2 h3 hq1 hq2 o m)
  rw [← hx.2]
  conv_lhs => rw [e]
  rfl

end GlobalTheory.FlagTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarLocalThetaFactorStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_local_theta_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
    Acts (evFin F v) (om' (g, h)) φ φ₁ →
    ∃ (c : ℂ) (P : GL (Fin a') (Fv F v)) (Q : GL (Fin (a + a')) (Fv F v)), ∀ Y, ι φ₁ Y = c * ι φ (P.1 * Y * Q.1) := by
  first | exact @GlobalTheory.OppLinOp.local_op_eq_smul | exact GlobalTheory.OppLinOp.local_op_eq_smul | (intros; apply GlobalTheory.OppLinOp.local_op_eq_smul <;> assumption)
end

