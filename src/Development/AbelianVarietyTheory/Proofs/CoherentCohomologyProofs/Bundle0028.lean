module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankCechLBHomologyExtProd
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechComplexAcyclicAdditiveLineBundleNoSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.PicZeroVan

theorem isIso_shear {C : Type*} [Category C] [CartesianMonoidalCategory C] (A : C) [GrpObj A] :
    IsIso (lift μ[A] (snd A A)) := by
  have hμ : μ[A] = fst A A * snd A A := by simp [Hom.mul_def]
  refine ⟨lift (fst A A * (snd A A)⁻¹) (snd A A), ?_, ?_⟩
  · ext
    · rw [Category.assoc, lift_fst, comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, hμ]
      simp
    · simp
  · ext
    · rw [Category.assoc, lift_fst, hμ, comp_mul, lift_fst, lift_snd]
      simp
    · simp

theorem isPullback_mul_snd {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    IsPullback μ[A].left (snd A A).left A.hom A.hom := by
  have h₀ : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    IsPullback.of_hasPullback A.hom A.hom
  have := isIso_shear A
  have : IsIso (lift μ[A] (snd A A)).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (lift μ[A] (snd A A))))
  have h₁ : IsPullback (lift μ[A] (snd A A)).left (snd A A).left (snd A A).left (𝟙 A.left) :=
    IsPullback.of_horiz_isIso ⟨by rw [← Over.comp_left, lift_snd, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz h₀
  rwa [← Over.comp_left, lift_fst, Category.id_comp] at h₂

theorem exists_fin_affine_cover (Z : Scheme.{0}) [CompactSpace Z] :
    ∃ (n : ℕ) (E : Fin n → Z.Opens), (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ := by
  obtain ⟨s, hs, e⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
    (X := Z) (U := Set.univ)).1 ⟨isCompact_univ, isOpen_univ⟩
  have := hs.fintype
  refine ⟨Fintype.card s, fun i => ((Fintype.equivFin s).symm i).1.1,
    fun i => ((Fintype.equivFin s).symm i).1.2, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (Set.univ : Set Z) := trivial
  rw [e] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, hx⟩ := hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨Fintype.equivFin s ⟨i, hi⟩, by simpa using hx⟩

theorem prod_res_pullU_one {X X' : Scheme.{0}} {J : Type} [Fintype J] (φ : J → (X' ⟶ X))
    (ε : J → ℤ) (W : X'.Opens) (V : J → X.Opens) (h : ∀ k, W ≤ φ k ⁻¹ᵁ V k) :
    ∏ k, res (h k) (pullU (φ k) (V k) 1) ^ ε k = 1 := by
  simp

theorem linComb_g_eq_one {X X' : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) {J : Type}
    [Fintype J] (φ : J → (X' ⟶ X)) (ε : J → ℤ) (i j : J → L.ι) :
    (L.LinComb φ ε).g i j = 1 := by
  have h := prod_res_pullU_one φ ε (L.wchart φ i ⊓ L.wchart φ j) (fun k => L.U (i k) ⊓ L.U (j k))
    (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ i k))
      (inf_le_right.trans (LB.wchart_le L φ j k)))
  simp only [← hL] at h
  exact h

theorem tw_pull_triv {X X' : Scheme.{0}} (N : LB X') (π : X' ⟶ X) :
    tw N ((Inh.trivLB X).pull π) 0 = tw N ((Inh.trivLB X).pull π) 1 := by
  have h : ∀ i j, ((Inh.trivLB X).pull π).g i j = 1 := fun i j =>
    linComb_g_eq_one (Inh.trivLB X) (fun _ _ => rfl) _ _ i j
  simp only [tw, pw, h, one_zpow]

theorem nontrivial_secOnR_triv {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X]
    (f : X ⟶ Spec (CommRingCat.of R)) : Nontrivial (SecOnR f (Inh.trivLB X) ⊤) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have : Nontrivial Γ(X, ⊤) := inferInstance
  exact ((SecOnR.of f _ ⊤).symm ≪≫ₗ secOnTrivEquiv ⊤).toEquiv.nontrivial

theorem cechLB_acyclic_of_additive : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → (∃ w : LB.Iso (M.pull μ[P.A].left) (tw (M.pull (fst P.A P.A).left) (M.pull (snd P.A P.A).left) 1), w.IsGen) → (∀ (σ : LB.Sec M) i, σ.f i = 0) → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → P.A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB P.A.hom M D).Acyclic := by
  intro K _ _ P M hM ⟨w, hw⟩ hσ κ _ _ D hD hD'
  obtain ⟨⟨hproj, hsep⟩, -⟩ := AbProj.abelian_projective_baseChange K P
  have := P.isAb.proper
  have hO := Inh.trivLB_isLB P.A.left
  have h₀ : IsPullback (fst P.A P.A).left (snd P.A P.A).left P.A.hom P.A.hom :=
    IsPullback.of_hasPullback P.A.hom P.A.hom
  have h₁ := isPullback_mul_snd P.A
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : QuasiCompact (fst P.A P.A).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) h₀.flip inferInstance
  have : CompactSpace (P.A ⊗ P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst P.A P.A).left
  have : Nonempty P.A.left := ⟨η[P.A].left (Classical.arbitrary (Spec (CommRingCat.of K)))⟩
  obtain ⟨k, E, hE, hE'⟩ := exists_fin_affine_cover (P.A ⊗ P.A).left
  have finM := cechLB_homology_finite_of_affine_cover K _ P.A.hom M κ D hM hsep hproj hD hD'
  have finO := cechLB_homology_finite_of_affine_cover K _ P.A.hom _ κ D hO hsep hproj hD hD'
  have k₀ := _root_.GlobalTheory.AbLaw.finrank_cechLB_homology_extProd K _ _ _ _ _ _ _ M M h₀ hM hM hsep hsep κ D κ D _ E hD hD' hD hD' hE hE'
    finM finM
  have k₁ := _root_.GlobalTheory.AbLaw.finrank_cechLB_homology_extProd K _ _ _ _ _ _ _ M _ h₁ hM hO hsep hsep κ D κ D _ E hD hD' hD hD' hE hE'
    finM finO
  have hf : μ[P.A].left ≫ P.A.hom = (fst P.A P.A).left ≫ P.A.hom :=
    (Over.w μ[P.A]).trans (Over.w (fst P.A P.A)).symm
  rw [hf, ← tw_pull_triv] at k₁
  have iso : cechLB ((fst P.A P.A).left ≫ P.A.hom)
      (tw (M.pull μ[P.A].left) ((Inh.trivLB P.A.left).pull (snd P.A P.A).left) 0) E ≅
      cechLB ((fst P.A P.A).left ≫ P.A.hom)
        (tw (M.pull (fst P.A P.A).left) (M.pull (snd P.A P.A).left) 1) E :=
    (cechLBTwZero _ E (LB.isLB_pull hM _) (LB.isLB_pull hO _)).symm ≪≫
      cechLBCongr _ E (LB.isLB_pull hM _) (isLB_tw (LB.isLB_pull hM _) (LB.isLB_pull hM _) 1) w hw
  have hO₀ : 0 < Module.finrank K ((cechLB P.A.hom (Inh.trivLB P.A.left) D).homology 0) := by
    obtain ⟨e⟩ := cechLB_homology_zero_equiv_sections K _ P.A.hom (Inh.trivLB P.A.left) κ D hD'
    have := nontrivial_secOnR_triv P.A.hom
    have := e.toEquiv.nontrivial
    have := finO 0
    exact Module.finrank_pos
  have hM₀ : Module.finrank K ((cechLB P.A.hom M D).homology 0) = 0 := by
    obtain ⟨e⟩ := cechLB_homology_zero_equiv_sections K _ P.A.hom M κ D hD'
    have : Subsingleton (LB.Sec M) := ⟨fun a b => by
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      congr 1
      funext i
      exact (hσ ⟨a, ha⟩ i).trans (hσ ⟨b, hb⟩ i).symm⟩
    have := (SecOnR.topEquiv P.A.hom M).toEquiv.subsingleton
    have := e.toEquiv.subsingleton
    exact Module.finrank_zero_of_subsingleton
  have key : ∀ n, Module.finrank K ((cechLB P.A.hom M D).homology n) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hz := k₀ n
      rw [Finset.sum_eq_zero fun x hx => ?_,
        ← (HomologicalComplex.homologyMapIso iso n).toLinearEquiv.finrank_eq, k₁ n,
        Finset.sum_eq_zero_iff] at hz
      · exact (mul_eq_zero.1 (hz (n, 0) (by simp))).resolve_right hO₀.ne'
      · have hx' : x.1 + x.2 = n := by simpa using hx
        rcases Nat.eq_zero_or_pos x.2 with h | h
        · rw [h, hM₀, mul_zero]
        · rw [ih x.1 (by omega), zero_mul]
  intro n
  have := finM n
  have : Subsingleton ((cechLB P.A.hom M D).homology n) := Module.finrank_zero_iff.1 (key n)
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_of_subsingleton _)

end GlobalTheory.PicZeroVan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSectionLiftFibreNoFirstCohomology
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw.FibreLift

theorem id_appLE {Y : Scheme.{0}} {U V : Y.Opens} (e : V ≤ (𝟙 Y : Y ⟶ Y) ⁻¹ᵁ U) (a : Γ(Y, U)) :
    ((𝟙 Y : Y ⟶ Y).appLE U V e).hom a = rs Y e a := rfl

theorem exists_sec_of_ker {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)}
    {M : LB Y} (P : Perf f M) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0) :
    ∃ s : LB.Sec M, ∀ i, rs Y (P.le i) (s.f (P.ch i)) = Seesaw.loc₀ P v i := by
  have h : IsPullback (𝟙 Y) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) Y (𝟙 Y) f h
  let t := E ⟨v, hv⟩
  have le : ∀ j, M.U j ≤ (M.pull (𝟙 Y)).U (fun _ => j) := fun j => le_pull M (𝟙 Y) le_rfl
  refine ⟨⟨fun j => rs Y (le j) (t.f fun _ => j), fun i j => ?_⟩, fun i => ?_⟩
  · have e := GlobalTheory.LB.sec_rel t (fun _ => i) (fun _ => j) (inf_le_left.trans (le i))
      (inf_le_right.trans (le j)) (inf_le_inf (le i) (le j))
    have e' := (GlobalTheory.LB.resG_pull_g (L := M) (𝟙 Y) (fun _ => i) (fun _ => j)
      (inf_le_inf (le i) (le j))).trans ((id_appLE _ _).trans (rs_self _ _))
    exact (rs_rs _ _ _).trans (e.trans (congrArg₂ (· * ·) e' (rs_rs _ _ _).symm))
  · exact (rs_rs _ _ _).trans (hE ⟨v, hv⟩ i)

theorem rs_topEquiv_smul {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R))
    (M : LB Y) (c : R) (x : SecOnR f M ⊤) (j : M.ι) {V : Y.Opens} (h : V ≤ M.U j) :
    rs Y h ((SecOnR.topEquiv f M (c • x)).f j) =
      cst f V c * rs Y h ((SecOnR.topEquiv f M x).f j) := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_base_smul, rs_rs, rs_rs, map_mul, rs_cst]

theorem exists_common_denominator {R K : Type} [CommRing R] [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) {n : ℕ} (z : Fin n → K) :
    ∃ (c : R) (w : Fin n → R), g c ≠ 0 ∧ g ∘ w = g c • z := by
  classical
  choose a b hb hab using fun i => hg (z i)
  refine ⟨∏ i, b i, fun i => a i * ∏ j ∈ Finset.univ.erase i, b j, ?_, funext fun i => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hb i
  · rw [← Finset.mul_prod_erase _ b (Finset.mem_univ i)]
    simp only [Function.comp_apply, map_mul, Pi.smul_apply, smul_eq_mul, ← hab]
    ring

theorem exists_pull_eq_smul : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y), Flat f → IsProjBy f → M.IsLB → ∀ (K : Type) [Field K] (g : R →+* K), (∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) → ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)) (h : IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g))), FirstCohomologyVanishes (M.pull π) → ∀ x₀ : SecOnR f₀ (M.pull π) ⊤, ∃ (c : R) (x : SecOnR f M ⊤), g c ≠ 0 ∧ SecOnR.pull M h.w ⊤ ⊤ le_top x = g c • x₀ := by
  intro R _ _ Y f M hf hp hM K _ g hg Y₀ π f₀ h hH x₀
  obtain ⟨P⟩ := nonempty_perf_of_noetherian R Y f hf hp M hM
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point R K g _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g Y₀ π f₀ h hH)
  obtain ⟨E, hE⟩ := P.sec K g Y₀ π f₀ h
  obtain ⟨v₀, hv₀⟩ := E.surjective (SecOnR.topEquiv f₀ _ x₀)
  obtain ⟨z, hz, -⟩ := hu K g hr.isUnit v₀.1 v₀.2
  obtain ⟨c, w, hc, hw⟩ := exists_common_denominator g hg z
  have hv : g ∘ B.mulVec w = g c • v₀.1 := by
    rw [← hz, ← Matrix.mulVec_smul, ← hw]
    exact funext fun j => RingHom.map_mulVec g _ _ j
  obtain ⟨s, hs⟩ := exists_sec_of_ker P (B.mulVec w)
    (by rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec])
  refine ⟨c, (SecOnR.topEquiv f M).symm s, hc, (SecOnR.topEquiv f₀ _).injective ?_⟩
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i)
    (fun i => le_pull M π (P.le i)) (fun y => Seesaw.exists_mem P (π y)) fun i => ?_
  have e₁ := Seesaw.loc_comp P h (B.mulVec w) i
  rw [hv, Seesaw.loc_smul, ← hs] at e₁
  have e₂ : Seesaw.loc P π f₀ v₀.1 i = _ := (hE v₀ i).symm
  rw [e₂, hv₀] at e₁
  refine Eq.trans ?_ ((rs_topEquiv_smul f₀ _ (g c) x₀ _ _).trans e₁).symm
  refine (rs_rs _ _ _).trans ?_
  refine (congrArg (rs Y₀ _) (SecOn.coord_pullLE π le_top _ _)).trans ?_
  refine (GlobalTheory.LB.resG_appLE π _ _ _).trans ?_
  refine (GlobalTheory.LB.appLE_resG π inf_le_right _ (s.f (P.ch i))).trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  exact (GlobalTheory.LB.appLE_resG π (P.le i) le_rfl _).symm

end GlobalTheory.AbLaw.FibreLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.MulFiniteAny

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem pw_one {X : Scheme.{0}} (H : LB X) : pw H ((1 : ℕ) : ℤ) = H := by
  cases H
  simp [AbLaw.pw]

theorem relAmple_of_veryAmpleBy' {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
    {L : LB A.left} (hL : L.IsLB) {M : ℕ} (s : Fin (M + 1) → LB.Sec L)
    (hA : VeryAmpleBy A.hom L s) : RelAmple A L := by
  have h : ∀ (s : Fin (M + 1) → LB.Sec (pw L ((1 : ℕ) : ℤ))),
      VeryAmpleBy A.hom (pw L ((1 : ℕ) : ℤ)) s → RelAmple A L :=
    fun s hs => GlobalTheory.Unif.relAmple_of_veryAmpleBy hL le_rfl s hs
  rw [pw_one] at h
  exact h s hA

theorem mul_eq_one_of_covolume_identity {G : Type} [CommGroup G] (a b c : G) :
    a * b ^ (-1 : ℤ) * c⁻¹ = (b * a⁻¹ * c)⁻¹ := by
  simp only [mul_inv, inv_inv, zpow_neg, zpow_one]
  rw [_root_.mul_comm a]

theorem exists_gen {X : Scheme.{0}} (L : LB X) (m : X ⟶ X) (e : ℤ)
    (w : LB.Iso (pw L e) (L.pull m)) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![e, -1]), α.IsGen := by
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![𝟙 X, m] j ≤
      (L.pull m).U (fun _ => j 1) ⊓ (pw L e).U (j 0) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1, Set.mem_iInter.1 hy 0⟩
  refine ⟨⟨fun j => (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩

  have val : ∀ p : Fin 2 → L.ι, y ∈ LB.wchart L (K := Fin 2) ![𝟙 X, m] p →
      gm (𝟙 X) y _ (res (le p) (w.s (fun _ => p 1, p 0)))⁻¹ =
        (gm (𝟙 X) y ((L.pull m).U (fun _ => p 1) ⊓ (pw L e).U (p 0)) (w.s (fun _ => p 1, p 0)))⁻¹ :=
    fun p hp => (map_inv _ _).trans (congrArg (·⁻¹) (gm_res (𝟙 X) y (le p) hp _))
  have hm : (𝟙 X : X ⟶ X) y ∈ (L.pull m).U (fun _ => p 1) ⊓ (pw L e).U (p 0) ⊓
      ((L.pull m).U (fun _ => q 1) ⊓ (pw L e).U (q 0)) := ⟨le p hy.1, le q hy.2⟩
  have e₀ := congrArg (gm (𝟙 X) y ((L.pull m).U (fun _ => p 1) ⊓ (pw L e).U (p 0) ⊓
      ((L.pull m).U (fun _ => q 1) ⊓ (pw L e).U (q 0))))
    (hw (fun _ => p 1, p 0) (fun _ => q 1, q 0))
  have e' := (gm_res (𝟙 X) y _ hm _).symm.trans (e₀.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (pw L e) (L.pull m) (𝟙 X) y (fun _ => p 1, p 0) (fun _ => q 1, q 0) hm)
    (gm_res (𝟙 X) y _ hm _))))
  have g₁ := gm_pull_g L m (𝟙 X) y (fun _ => p 1) (fun _ => q 1) hm.1.1 hm.2.1
  have g₂ : gm (𝟙 X) y ((pw L e).U (p 0) ⊓ (pw L e).U (q 0)) ((pw L e).g (p 0) (q 0)) =
      gm (𝟙 X) y (L.U (p 0) ⊓ L.U (q 0)) (L.g (p 0) (q 0)) ^ e := map_zpow _ _ _
  have g₃ : gm (𝟙 X) y _ ((LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![e, -1]).g p q) =
      gm (𝟙 X) y (L.U (p 0) ⊓ L.U (q 0)) (L.g (p 0) (q 0)) ^ e *
        gm (𝟙 X ≫ m) y (L.U (p 1) ⊓ L.U (q 1)) (L.g (p 1) (q 1)) ^ (-1 : ℤ) := by
    refine (gm_linComb L ![𝟙 X, m] ![e, -1] (𝟙 X) y p q hy.1 hy.2).trans ?_
    rw [Fin.prod_univ_two]
    rfl
  have e'' := e'.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) g₁ (congrArg (·⁻¹) g₂)) rfl)
  refine ((gm_res (𝟙 X) y _ hy _).trans (val p hy.1)).trans ((congrArg (·⁻¹) e'').trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) g₃ ((gm_res (𝟙 X) y _ hy _).trans (val q hy.2))).trans ?_)
  exact mul_eq_one_of_covolume_identity _ _ _

theorem isFinite_mulA : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → IsFinite (mulA B n).left := by
  intro K _ _ B _ hB n hn
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple K B hB
  obtain ⟨w, hw⟩ := GlobalTheory.MulPullAny.mulPull_of_symm K B hB H hH hsym n
  obtain ⟨α, hα⟩ := exists_gen H (mulA B n).left _ w hw
  have := hB.proper
  exact GlobalTheory.MulFinite.isFinite_of_relAmple B H hH (relAmple_of_veryAmpleBy' hH s hs) _ (n ^ 2)
    (by positivity) α hα

end GlobalTheory.MulFiniteAny
end
end

