module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureSectionRatiosGenerateFunctions
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpScheme
section
noncomputable section

namespace GlobalTheory.SS.InvFrame

theorem exists_det_ne_zero {F S : Type} [Field F] {n : ℕ} (D : Fin n → S → F) (h : LinearIndependent F D) :
    ∃ t : Fin n → S, (Matrix.of fun i j => D i (t j)).det ≠ 0 := by
  have hs := span_flip_eq_top_iff_linearIndependent.2 h
  obtain ⟨f, hf, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq F (Set.range (flip D))
  have e : Module.finrank F (Submodule.span F (Set.range (flip D))) = n := by
    rw [hs, finrank_top, Module.finrank_fin_fun]
  choose t ht using hf
  refine ⟨fun j => t (j.cast e.symm), ?_⟩
  have h2 := hli.comp (Fin.cast e.symm) (Fin.cast_injective _)
  refine ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)).ne_zero
  have e2 : (Matrix.of fun i j : Fin n => D i (t (j.cast e.symm))).col = f ∘ Fin.cast e.symm :=
    funext fun j => ht _
  rw [e2]
  exact h2

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis constFn)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.KS GlobalTheory.KS.InvField

theorem value_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {T : CommRingCat.{0}}
    (φ : Γ(X, U) ⟶ T) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso T).hom.hom (pbT (Spec.map φ ≫ hU.fromSpec) f ⊤) = φ.hom f := by
  have ht : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have ht' : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := fun q _ => ht (x := Spec.map φ q) trivial
  rw [pbT_of_le _ ht']
  have h1 : hU.fromSpec.appLE U ⊤ ht = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h2 : (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ ht' ≫ (Scheme.ΓSpecIso T).hom = φ := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) _ U ⊤ ⊤ ht le_top, h1, Category.assoc, Iso.inv_comp_eq,
      ← Scheme.ΓSpecIso_naturality]
    congr 1
  exact congrArg (fun q => q.hom f) h2

theorem value_constFn_id {T : Type} [CommRing T] (a : T) :
    (Scheme.ΓSpecIso (.of T)).hom.hom (constFn (𝟙 (Sp T)) ⊤ a) = a := by
  have h : (𝟙 (Sp T) : Sp T ⟶ Sp T).appLE ⊤ ⊤ (fun _ _ => trivial) = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 (Sp T)) (U := ⊤)).trans rfl
  rw [constFn, h]
  exact congrArg (fun q => q.hom a) (Scheme.ΓSpecIso (.of T)).inv_hom_id

variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))} [GrpObj G] [IsCommMonObj G]

theorem exists_independent [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {S F : Type} [CommRing S] [Algebra K S] [Field F] [Algebra K F] (j : sp (R₀ := K) S ⟶ G)
    [IsOpenImmersion j.left] (u : S →ₐ[K] F) :
    ∃ D : Fin n → S → F, LinearIndependent F D ∧ ∀ k, ∃ φ : S →ₐ[K] DualNumber F,
      spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v k) *
        (spMap ((inlS K F).comp u) ≫ j) ∧ ∀ a, (φ a).snd = D k a := by
  obtain ⟨χ, hχ, hfst⟩ := exists_chart_pt_of_nil j (TrivSqZeroExt.fstHom K F (Fin n → F))
    (fun a => ⟨inl a, rfl⟩) (fun a ha => ⟨2, by
      rw [pow_two]; exact mul_eq_zero_of_sq (ker_fst_sq (R := K) (S := F) (Fin n → F)) ha ha⟩)
    (lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) *
      (spMap ((TrivSqZeroExt.inlAlgHom K F (Fin n → F)).comp u) ≫ j)) u (by
      rw [MonObj.comp_mul, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), one_mul, ← Category.assoc,
        spMap_comp]
      rfl)
  have hfst : ∀ a, (χ a).fst = u a := AlgHom.congr_fun hfst
  let φ : (Fin n → F) → (S →ₐ[K] DualNumber F) := fun c => (vecTo (inlS K F) (fun i => inr (c i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = tanExp v c * (spMap ((inlS K F).comp u) ≫ j) := fun c => by
    rw [← spMap_comp, Category.assoc, ← hχ, MonObj.comp_mul, comp_lieExp, ← Category.assoc, spMap_comp]
    congr 1
    · exact lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _
    · congr 2
      exact AlgHom.ext fun a => by simp [vecTo_apply]
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, c k * (χ a).snd k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  refine ⟨fun k a => (χ a).snd k, Fintype.linearIndependent_iff.2 fun c hc k => ?_,
    fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · have : φ c = φ 0 := AlgHom.ext fun a => TrivSqZeroExt.ext (by rw [hφ1, hφ1]) (by
      rw [hφ2, hφ2]
      simpa using congrFun hc a)
    have h3 := mul_right_cancel ((hφ c).symm.trans (this ▸ hφ 0))
    have h4 := (expBij (DualNumber F) hv _ (ker_fst_sq (R := K) (S := F) F)).1 _ _ (fun _ => rfl) (fun _ => rfl) _ _ h3
    exact TrivSqZeroExt.inr_injective (congrFun h4 k)
  · rw [hφ]
    congr 1
    refine (Finset.prod_eq_single k (fun i _ hi => epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _
      (by simp [Pi.single_eq_of_ne hi]) _) (by simp)).trans ?_
    congr 3
    simp
  · rw [hφ2]
    simp [Pi.single_apply]


omit [IsCommMonObj G] in
theorem value_invDer {v : epsR K ⟶ G} {dd : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(G.left, W)} (hd : IsInvDer v dd)
    {U : G.left.Opens} (hU : IsAffineOpen U) [Algebra K Γ(G.left, U)] (j : sp (R₀ := K) Γ(G.left, U) ⟶ G)
    (hj : j.left = hU.fromSpec) {F : Type} [Field F] [Algebra K F] (u : Γ(G.left, U) →ₐ[K] F)
    (φ : Γ(G.left, U) →ₐ[K] DualNumber F)
    (hφ : spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v) *
        (spMap ((inlS K F).comp u) ≫ j)) (f : Γ(G.left, U)) : (φ f).snd = u (dd U f) := by
  let w : sp (R₀ := K) (DualNumber F) ⟶ epsR K ⊗ G :=
    lift (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))) (spMap ((inlS K F).comp u) ≫ j)
  have e1 : w.left ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, ← hφ, Over.comp_left, hj]
    rfl
  have e2 : w.left ≫ (snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom ((inlS K F).comp u).toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, lift_snd, Over.comp_left, hj]
    rfl
  have e3 : w.left ≫ (fst (epsR K) G).left = 𝟙 _ ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
      (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)).toRingHom := by
    rw [← Over.comp_left, lift_fst, Category.id_comp]
    rfl
  have hw : ⊤ ≤ w.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, e2]
    exact fun q _ => hU.fromSpec_preimage_self.ge (x := Spec.map _ q) trivial
  have key : ∀ f : Γ(G.left, U), ((Scheme.ΓSpecIso (.of (DualNumber F))).hom.hom (pbT w.left
      (pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left f ((snd (epsR K) G).left ⁻¹ᵁ U)) ⊤) : DualNumber F) =
      inl (u f) + inr 1 * inl (u (dd U f)) := fun f => by
    rw [hd U f, pbT_add, pbT_mul, pbT_pbT _ _ le_rfl hw, pbT_pbT _ _ le_rfl hw, pbT_constFn _ _ hw, e2, e3,
      constFn_spMap, map_add, map_mul]
    refine congrArg₂ _ (value_fromSpec hU _ _) (congrArg₂ _ ?_ (value_fromSpec hU _ _))
    refine Eq.trans ?_ (epsTo_eps (R := K) (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))
    exact value_constFn_id _
  by_cases h : (snd (epsR K) G).left ⁻¹ᵁ U ≤ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ U
  · have := key f
    rw [pbT_pbT _ _ h hw, e1] at this
    have h5 := congrArg TrivSqZeroExt.snd ((value_fromSpec hU _ f).symm.trans this)
    simpa using h5
  · have := key 1
    rw [show pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left (1 : Γ(G.left, U))
      ((snd (epsR K) G).left ⁻¹ᵁ U) = 0 from dif_neg h, pbT_zero, map_zero] at this
    simpa using congrArg TrivSqZeroExt.fst this

theorem exists_mem_basicOpen [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    (D : Fin n → VF G) (hd : ∀ i, IsInvDer (v i) fun W f => (D i).D W f) (x : G.left) :
    ∃ (U : G.left.Opens) (t : Fin n → Γ(G.left, U)), x ∈ G.left.basicOpen (jac D U t) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  letI : Algebra K Γ(G.left, U) := (Spec.preimage (hU.fromSpec ≫ G.hom)).hom.toAlgebra
  let j : sp (R₀ := K) Γ(G.left, U) ⟶ G := Over.homMk hU.fromSpec (Spec.map_preimage _).symm
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hx
  have := PrimeSpectrum.isPrime p
  let u : Γ(G.left, U) →ₐ[K] (PrimeSpectrum.asIdeal p).ResidueField := IsScalarTower.toAlgHom _ _ _
  obtain ⟨δ, hδ, hφ⟩ := exists_independent hv j u
  obtain ⟨t, ht⟩ := exists_det_ne_zero δ hδ
  refine ⟨U, t, ?_⟩
  have h1 : u (jac D U t) ≠ 0 := by
    rw [jac, AlgHom.map_det]
    refine (congrArg Matrix.det (Matrix.ext fun i k => ?_)).trans_ne ht
    obtain ⟨φ, h2, h3⟩ := hφ i
    exact (value_invDer (hd i) hU j rfl u φ h2 (t k)).symm.trans (h3 _)
  have h2 : p ∈ hU.fromSpec ⁻¹ᵁ G.left.basicOpen (jac D U t) := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact fun h => h1 (Ideal.algebraMap_residueField_eq_zero.2 h)
  exact h2

end GlobalTheory.SS.InvFrame

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.SS.exists_isFrame : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∃ D : Fin g → VF A, IsFrame D := by
  intro K _ A _ _ g hg
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  choose dd hdd using fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).1
  have hp := fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).2 _ (hdd i)
  let D : Fin g → VF A := fun i =>
    { D := fun U => AddMonoidHom.mk' (dd i U) ((hp i).1 U)
      leibniz := (hp i).2.1
      const := (hp i).2.2.2.1
      res := fun U V h a => by
        have := (hp i).2.2.1 U V a h
        rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h] at this
        exact this }
  refine ⟨D, by rwa [Fintype.card_fin], fun x => ?_⟩
  obtain ⟨U, t, hx⟩ := InvFrame.exists_mem_basicOpen hv D hdd x
  have hle := A.left.basicOpen_le (jac D U t)
  refine ⟨_, fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i), hx, ?_⟩
  have e : jac D _ (fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i)) =
      (A.left.presheaf.map (homOfLE hle).op).hom (jac D U t) := by
    exact (congrArg Matrix.det (Matrix.ext fun i k => (D i).res U _ hle (t k))).trans
      (RingHom.map_det (A.left.presheaf.map (homOfLE hle).op).hom (Matrix.of fun i k => (D i).D U (t k))).symm
  rw [e]
  exact A.left.toRingedSpace.isUnit_res_basicOpen (jac D U t)

end

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosedImm

section Lattice
variable {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (N : ℕ)

def Alone (ε : X) : Prop := ∀ v : X, v ≠ 0 → q ε < q (ε + N • v)

variable {q N}

theorem Alone.short {ε : X} (h : Alone q N ε) : Short q N ε := fun m => by
  by_cases hm : m = 0
  · simp [hm]
  · exact (h m hm).le

theorem Alone.eq {ε β m : X} (h : Alone q N ε) (hβ : Short q N β) (e : β = ε + N • m) : β = ε := by
  by_cases hm : m = 0
  · simp [e, hm]
  · have h1 := hβ (-m)
    have h2 := h m hm
    rw [e] at h1
    simp only [smul_neg, add_neg_cancel_right] at h1
    exact absurd h2 (not_lt.2 h1)

theorem pos_of_tendsto [Module.Free ℤ X] (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {v : X}
    (hv : v ≠ 0) : 0 < q v := by
  by_contra hn
  have hfin : {x : X | ¬ 0 < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • v) (smul_left_injective ℤ hv)
    (fun n => ?_) hfin
  change ¬ 0 < q (n • v)
  rw [q.map_smul, zsmul_eq_mul, Int.cast_mul]
  exact not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) (not_lt.1 hn))

theorem alone_zero [Module.Free ℤ X] (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (hN : N ≠ 0) :
    Alone q N (0 : X) := fun v hv => by
  rw [map_zero, zero_add]
  refine pos_of_tendsto hq ?_
  rw [← natCast_zsmul]
  exact smul_ne_zero (by exact_mod_cast hN) hv

end Lattice

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (e : U ≤ V) (a : R) : resG X e (constFn p V a) = constFn p U a := by
  unfold constFn
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  erw [Scheme.Hom.appLE_map]

theorem const_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

theorem isRatio_lin {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {H : LB X} {J : Type} [Fintype J]
    {s : J → H.Sec} {a : J → k} {φ t : H.Sec} (h : IsLin p s a φ) {W : X.Opens} {r : J → Γ(X, W)}
    (hr : ∀ j, IsRatio (s j) t W (r j)) : IsRatio φ t W (∑ j, constFn p W (a j) * r j) := fun l => by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h l, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, res_const, res_const, hr j l, _root_.mul_assoc]

variable {k : Type} [Field k] (Φ : FibPre k)

theorem isLB_H (d : ℕ) : (Φ.H d).IsLB := by
  have key : ∀ (U V : Φ.E.B.left.Opens) (h : V ≤ U) (h' : Φ.D.q.left ⁻¹ᵁ V ≤ Φ.D.q.left ⁻¹ᵁ U)
      (u : Γ(Φ.E.B.left, U)ˣ),
      res h' (pullU Φ.D.q.left U u ^ d) = pullU Φ.D.q.left V (res h u) ^ d := by
    intro U V h h' u
    rw [map_pow]
    congr 1
    ext
    exact (congrArg (fun φ => φ.hom (u : Γ(Φ.E.B.left, U))) (Φ.D.q.left.naturality (homOfLE h).op)).symm
  refine ⟨?_, fun i => ?_, fun i j l => ?_⟩
  · show ⨆ l, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l = ⊤
    rw [← Scheme.Hom.preimage_iSup, Φ.isLB.cover]; rfl
  · have := congrArg (fun u => pullU Φ.D.q.left _ u ^ d) (Φ.isLB.g_self i)
    simp only [map_one, one_pow] at this
    exact (key _ _ _ (Scheme.Hom.preimage_mono _ (le_inf le_rfl le_rfl)) _).trans this
  · have := congrArg (fun u => pullU Φ.D.q.left _ u ^ d) (Φ.isLB.cocycle i j l)
    simp only [map_mul, mul_pow] at this
    rw [← key _ _ _ (Scheme.Hom.preimage_mono _ inf_le_left),
      ← key _ _ _ (Scheme.Hom.preimage_mono _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right)),
      ← key _ _ _ (Scheme.Hom.preimage_mono _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right))] at this
    exact this

theorem isRatio_pull {s t : Φ.N₀.Sec} {φ ψ : (Φ.H 1).Sec}
    (hφ : ∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (s.f l))
    (hψ : ∀ l, ψ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l))
    {V : Φ.E.B.left.Opens} {r : Γ(Φ.E.B.left, V)} (h : IsRatio s t V r) :
    IsRatio φ ψ (Φ.D.q.left ⁻¹ᵁ V) ((Φ.D.q.left.app V).hom r) := fun l => by
  have e := congrArg (Φ.D.q.left.app (V ⊓ Φ.N₀.U l)).hom (h l)
  rw [map_mul, app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right),
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_left),
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right)] at e
  rw [hφ, hψ]
  exact e

variable {Φ} {N : ℕ} {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X}
  {F : J → (Φ.H 1).Sec}

theorem pure_of_alone (hG : Φ.Good N q cls F) {ε : Φ.E.X} (hε : Alone q N ε) {i : J} (hi : cls i = ε) :
    Φ.Pure ε (F i) := fun β hβ => by
  obtain ⟨h1, m, hm⟩ := hG.supp i β hβ
  exact hε.eq h1 (hi ▸ hm)

theorem onto_of_alone (hG : Φ.Good N q cls F) {ε : Φ.E.X} (hε : Alone q N ε) {φ : (Φ.H 1).Sec}
    (hφ : Φ.Pure ε φ) : ∃ a : J → k, (∀ i, a i ≠ 0 → cls i = ε) ∧
      ∀ l, Φ.wt φ ε l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) ε l := by
  obtain ⟨a, ha, h⟩ := hG.onto ε hε.short φ hφ
  refine ⟨a, fun i hi => ?_, h⟩
  obtain ⟨m, hm⟩ := ha i hi
  exact hε.eq (m := -m) (hG.short i) (by rw [hm]; simp)

theorem isLin_of_alone (hG : Φ.Good N q cls F) {ε : Φ.E.X} (hε : Alone q N ε) {φ : (Φ.H 1).Sec}
    (hφ : Φ.Pure ε φ) : ∃ a : J → k, IsLin Φ.G.hom F a φ := by
  obtain ⟨a, ha, h⟩ := onto_of_alone hG hε hφ
  refine ⟨a, fun l => eq_of_weight_eq Φ.D (Φ.ch l) _ (Φ.aff l) (Φ.le l) fun χ => ?_⟩
  refine Eq.trans ?_ (WtLin.weight_sum Φ F a χ l).symm
  by_cases hχ : χ = ε
  · subst hχ
    exact h l
  · have h0 : Φ.wt φ χ l = 0 := by
      by_contra hne
      exact hχ (hφ ⟨l, hne⟩)
    refine h0.trans (Finset.sum_eq_zero fun i _ => ?_).symm
    by_cases hi : a i = 0
    · rw [hi, const_zero, zero_mul]
    · have h1 : Φ.wt (F i) χ l = 0 := by
        by_contra hne
        exact hχ (pure_of_alone hG hε (ha i hi) ⟨l, hne⟩)
      rw [h1, mul_zero]

theorem immBy_weight_zero : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → ImmBy Φ.G.hom (Φ.H 1) F {i | cls i = 0}) := by
  intro hL hL2 k _ _ Φ g N N' q J _ cls F π hB hG hg
  classical
  have h4 := hB.four
  have h0 : Alone q N (0 : Φ.E.X) := alone_zero hG.pos (by omega)
  obtain ⟨e, he, -⟩ := GlobalTheory.exists_basis_unique_min_and_sums_separated Φ.E.X q hG.pos _ g N N' _ rfl
    (by omega) hB.lll hB.sep
  have hp : ∀ i : {i // cls i = 0}, Φ.Pure 0 (F i.1) := fun i => pure_of_alone hG h0 i.2
  choose τ hτ₁ hτ₂ hτ₃ using fun i => (FibPre.pure_zero k Φ).2 _ (hp i)
  obtain ⟨m, t, ht⟩ := _root_.GlobalTheory.VeryAmpleMove.exists_immBy_abelianPart hL hL2 k Φ N h4 π
  have := Φ.E.isAbelian.proper
  obtain ⟨hcov, hloc⟩ := _root_.GlobalTheory.ZH.SpanImm.immBy_of_span k _ Φ.E.B.hom Φ.N₀ Φ.isLB _ _ t τ ht fun n => by
    obtain ⟨φ, hφ, hφ'⟩ := (FibPre.pure_zero k Φ).1 (t n)
    obtain ⟨a, ha, h⟩ := onto_of_alone hG h0 hφ
    refine ⟨fun i => a i.1, fun l => ?_⟩
    rw [← hφ', h, ← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = 0),
      Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {i // ¬ cls i = 0} =>
        constFn Φ.E.B.hom _ (a i.1) * Φ.wt (F i.1) 0 l) fun i _ => by
          have : a i.1 = 0 := by_contra fun hne => i.2 (ha _ hne)
          rw [this, const_zero, zero_mul], add_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [hτ₁]
  refine ⟨?_, fun i hi => ?_⟩
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (show Φ.D.q.left x ∈ ⊤ from trivial))
    obtain ⟨-, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i.1, TopologicalSpace.Opens.mem_iSup.2 ⟨i.2, ?_⟩⟩
    rw [hτ₃]
    exact hi
  · obtain ⟨haff, ρ, hρ, hgen⟩ := hloc ⟨i, hi⟩ trivial
    have hle := (hτ₃ ⟨i, hi⟩).ge
    have hu := fun s => SecRatio.existsUnique_isRatio (isLB_H Φ 1) s (F i) _ hle
    have := Φ.D.q_affine
    rw [hτ₃ ⟨i, hi⟩]
    choose r hr hr' using fun j => hu (F j)
    refine ⟨haff.preimage _, r, hr, ?_⟩
    refine _root_.GlobalTheory.ZH.WtGen.ratios_generate k Φ _ e (F i) _ haff (hp ⟨i, hi⟩) hle (GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at hL hL2 k Φ N h4 π) _
      (fun a => ?_) fun n φ y hφ hy => ?_
    · have ha : a ∈ Subring.closure _ := hgen.ge (Subring.mem_top a)
      refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ ha)
      rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
      · exact Subring.subset_closure (Or.inl ⟨c, (WtLin.app_constFn _ _ _ (Over.w Φ.D.q) _ c).symm⟩)
      · exact Subring.subset_closure (Or.inr ⟨j.1,
          (hr' _ _ (isRatio_pull Φ (hτ₂ j) (hτ₂ ⟨i, hi⟩) (hρ j))).symm⟩)
    · obtain ⟨a, ha⟩ : ∃ a : J → k, IsLin Φ.G.hom F a φ :=
        hφ.elim (isLin_of_alone hG fun v hv => (he n v hv).1) (isLin_of_alone hG fun v hv => (he n v hv).2)
      rw [(hu φ).unique hy (isRatio_lin _ ha hr)]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

end GlobalTheory.ZH.ClosedImm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperHomOfRelAmple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem isProper_hom_of_relAmple {T : Scheme.{0}} {A : Over T} [GrpObj A] {B : LB A.left} (h : RelAmple A B) :
    IsProper A.hom := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (fun U : T.affineOpens => U.1)
    (iSup_affineOpens_eq_top T) fun U => ?_
  have h₁ := projProper _ _ _ (GlobalTheory.ProjSpace.isProjOver_morphismRestrict_of_relAmple h U.2)
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper) _ U.2.isoSpec.hom).1 h₁

theorem abOpen_of_isOpen_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → IsOpen (abLocus Z.G) → GlobalTheory.Models.AbOpen Z.G := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Z _ hO
  letI := Z.grp
  let W : M.Z.Opens := ⟨abLocus Z.G, hO⟩
  refine ⟨W, rfl, ?_⟩
  have h : IsProper (pullback.snd Z.G.hom W.ι) := isProper_hom_of_relAmple (Z.pol W le_rfl).1
  unfold morphismRestrict
  infer_instance

end GlobalTheory.ZH
end

