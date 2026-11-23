module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExAtMemPairChartIff
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)ˣ) :
    res h₂ (res h₁ a) = res (h₂.trans h₁) a := by
  unfold res
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private lemma U_le_pull_id_U {X : Scheme.{0}} (N : LB X) (i : N.ι) :
    N.U i ≤ (N.pull (𝟙 X)).U (fun _ => i) := by
  intro x hx
  unfold LB.pull LB.LinComb LB.wchart
  simpa using hx

private lemma res_pullU_id_moduli {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (h' : V ≤ U)
    (a : Γ(X, U)ˣ) : res h (pullU (𝟙 X) U a) = res h' a := by
  unfold res pullU
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rfl

private lemma res_self_moduli {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by
  unfold res
  ext
  simp

theorem exists_gen_of_pull_id {X : Scheme.{0}} (N : LB X) (t : (N.pull (𝟙 X)).Gen) (ht : t.IsGen) :
    ∃ t : N.Gen, t.IsGen := by
  refine ⟨⟨fun i => res (U_le_pull_id_U N i) (t.s (fun _ => i))⟩, ?_⟩
  intro i j
  have key := congrArg (res (inf_le_inf (U_le_pull_id_U N i) (U_le_pull_id_U N j))) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, res_res_lemma, res_res_lemma] at key
  simp only [res_res_lemma]
  refine key.trans ?_
  congr 1
  have hle : (N.pull (𝟙 X)).U (fun _ => i) ⊓ (N.pull (𝟙 X)).U (fun _ => j) ≤ (𝟙 X) ⁻¹ᵁ (N.U i ⊓ N.U j) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    simp only [LB.pull, LB.LinComb, LB.wchart] at h1 h2
    have a : x ∈ N.U i := by simpa using h1
    have b : x ∈ N.U j := by simpa using h2
    exact ⟨a, b⟩
  have hG : (N.pull (𝟙 X)).g (fun _ => i) (fun _ => j) = res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j)) := by
    show ∏ _k : PUnit, (res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [hG, res_res_lemma]
  exact (res_pullU_id_moduli _ le_rfl _).trans (res_self_moduli _ _)

private theorem val_mul_val_comm_of_fst_eq (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} (π : S' ⟶ S) (A : Over S) [GrpObj A]
    (N : LB A.left) (hA : IsAbelianScheme A) (hN : N.IsLB)
    (w : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen) (hw : w.IsGen)
    (e' : S' ⟶ pullback A.hom π) (he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A)
    (he'q : e' ≫ pullback.snd A.hom π = 𝟙 S')
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ pullback A.hom π)
    (hg : g₁ ≫ pullback.fst A.hom π = g₂ ≫ pullback.fst A.hom π) (z : Z) (J : (Z ⟶ A.left) → N.ι)
    (hJ : Good N z J) :
    val w g₁ z J * val w (g₂ ≫ pullback.snd A.hom π ≫ e') z J =
      val w g₂ z J * val w (g₁ ≫ pullback.snd A.hom π ≫ e') z J := by
  have hπ : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
    rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
  let FinalForm : Over S := Over.mk (g₁ ≫ pullback.snd A.hom π ≫ π)
  have hw1 : (fst A FinalForm).left ≫ A.hom = (snd A FinalForm).left ≫ (g₁ ≫ pullback.snd A.hom π ≫ π) :=
    (Over.w (fst A FinalForm)).trans (Over.w (snd A FinalForm)).symm
  let a : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₁ ≫ pullback.snd A.hom π) (by rw [hw1]; simp)
  let a' : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₂ ≫ pullback.snd A.hom π) (by rw [hw1, hπ]; simp)
  let p0 : (A ⊗ FinalForm).left ⟶ Z := (snd A FinalForm).left
  let e : Z ⟶ (A ⊗ FinalForm).left := (lift (toUnit FinalForm ≫ η[A]) (𝟙 FinalForm)).left
  have he : e ≫ p0 = 𝟙 Z := by
    simp only [e, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hap : a ≫ pullback.fst A.hom π = a' ≫ pullback.fst A.hom π := by
    simp only [a, a', pullback.lift_fst]
  have hU : (toUnit FinalForm).left = g₁ ≫ pullback.snd A.hom π ≫ π :=
    (Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))
  have hea : e ≫ a = g₁ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a, e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU]
      rfl
    · simp only [a, e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have hea' : e ≫ a' = g₂ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a', e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU, hπ]
      rfl
    · simp only [a', e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  let x : FinalForm ⟶ A := Over.homMk (g₁ ≫ pullback.fst A.hom π) (by simp [FinalForm, pullback.condition])
  let ρ : Z ⟶ (A ⊗ FinalForm).left := (lift x (𝟙 FinalForm)).left
  have hρp : ρ ≫ p0 = 𝟙 Z := by
    simp only [ρ, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hρa : ρ ≫ a = g₁ := by
    apply pullback.hom_ext
    · simp only [a, ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst]
      rfl
    · simp only [a, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  have hρa' : ρ ≫ a' = g₂ := by
    apply pullback.hom_ext
    · simp only [a', ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst, ← hg]
      rfl
    · simp only [a', Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  let u := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a) (LB.pullGen N _ _ w (p0 ≫ e ≫ a'))
  let u' := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a') (LB.pullGen N _ _ w (p0 ≫ e ≫ a))
  have hu : u.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hu' : u'.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a') (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hF : FormEq (Sum.elim (fun _ : PUnit.{1} => a' ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a) ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1))
      (Sum.elim (fun _ : PUnit.{1} => a ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a') ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1)) := by
    intro U _ h
    simp [Fintype.prod_sum_type, hap]
  have key := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gen_unique' hN hF p0 e he
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_snd hG hA FinalForm) hu hu' ?_ Z ρ z J hJ
  · simp only [u, u'] at key
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ] at key
    have hρp' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), ρ ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, hρp, Category.id_comp]
    rw [hρp', hρp', hea', hea, hρa, hρa'] at key
    exact key
  · intro y J' hJ'
    simp only [u, u']
    rw [val_mul hJ', val_mul hJ', val_pull hJ', val_pull hJ', val_pull hJ', val_pull hJ']
    have he' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), e ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, he, Category.id_comp]
    rw [he', he', mul_comm]

theorem exists_gen_of_rigidified_of_flat_baseChange :
    Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro hG S S' π A _ N hA hN hfl hsu hqc hr hw
  obtain ⟨r, hr⟩ := hr
  obtain ⟨w, hw⟩ := hw
  have := hfl
  have := hsu
  have := hqc
  have hz : (π ≫ eSec A) ≫ A.hom = 𝟙 S' ≫ π := by
    rw [Category.assoc, Category.id_comp]
    have h0 : (η[A]).left ≫ A.hom = 𝟙 S := Over.w (η[A])
    unfold eSec
    rw [h0, Category.comp_id]
  let e' : S' ⟶ pullback A.hom π := pullback.lift (π ≫ eSec A) (𝟙 S') hz
  have he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A := pullback.lift_fst _ _ _
  have he'q : e' ≫ pullback.snd A.hom π = 𝟙 S' := pullback.lift_snd _ _ _
  let w' : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen := w
  have hw' : w'.IsGen := hw
  let r' : (N.LinComb (fun _ : PUnit.{1} => eSec A) (fun _ => (1 : ℤ))).Gen := r
  have hr' : r'.IsGen := hr
  let v := LB.mulGen N _ _ _ _ w' (LB.mulGen N _ _ _ _ (LB.pullGen N _ _ r' (pullback.snd A.hom π ≫ π))
    (LB.invGen N _ _ (LB.pullGen N _ _ w' (pullback.snd A.hom π ≫ e'))))
  have hv : v.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ hw'
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ r' hr' _)
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w' hw' _)))
  obtain ⟨t', ht', hvv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
    (φ' := fun _ : PUnit.{1} => pullback.fst A.hom π ≫ 𝟙 A.left) (ε' := fun _ => (1 : ℤ))
    (by intro U _ h; simp [Fintype.prod_sum_type, he'p]) v hv
  refine Exists.elim (GlobalTheory.CubeDescent.exists_gen_descend hN (pullback.fst A.hom π)
    (fun _ : PUnit.{1} => 𝟙 A.left) (fun _ => (1 : ℤ)) t' ht' ?_) (fun t ht => exists_gen_of_pull_id N t ht)
  · intro Z g₁ g₂ z J hJ hg
    rw [hvv Z g₁ z J hJ, hvv Z g₂ z J hJ]
    simp only [v, val_mul hJ, val_pull hJ, val_inv]
    have hq : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
      rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
    rw [hq]
    have key := val_mul_val_comm_of_fst_eq hG π A N hA hN w' hw' e' he'p he'q g₁ g₂ hg z J hJ
    rw [mul_left_comm (val w' g₁ z J), mul_left_comm (val w' g₂ z J)]
    congr 1
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolLinearLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

namespace GlobalTheory.LocLift

noncomputable section

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

theorem exists_hol_linear_lift {B : Set (Fin m → ℂ)} (hB : IsOpen B) {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ} (hr : 0 < r)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    (f : G ⟶ G) [IsMonHom f] :
    ∃ L : (Fin m → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ b ∈ B, ∀ z, e b (L b z) = e b z ≫ f) ∧
      ∀ z, DifferentiableOn ℂ (fun b => L b z) B := by
  have key : ∀ b₁ ∈ B, ∃ L : (Fin m → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ᶠ b in 𝓝 b₁, ∀ z, e b (L b z) = e b z ≫ f) ∧ ∀ z, DifferentiableAt ℂ (fun b => L b z) b₁ := by
    intro b₁ hb₁
    obtain ⟨ζ, -, h2, h3⟩ := hl.lift (W := B ×ˢ Set.univ) (β := Prod.fst)
      (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2 ≫ f) (w₀ := (b₁, 0)) (z₀ := 0)
      (hB.prod isOpen_univ) ⟨hb₁, trivial⟩ differentiableOn_fst (fun _ h => h.1) (isHolTo_comp_hom hol f.left)
      (by simp only [hom_zero (he b₁ hb₁).1.1, MonObj.one_comp])
    refine ⟨fun b => ((fderiv ℂ ζ (b, 0)).comp (ContinuousLinearMap.inr ℂ _ _)).toLinearMap, ?_, fun z => ?_⟩
    · have ht : Tendsto (fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) (𝓝 b₁) (𝓝 (b₁, 0)) :=
        (Continuous.prodMk_left _).tendsto _
      filter_upwards [hB.mem_nhds hb₁, ht.eventually h2.eventually_analyticAt, ht.eventually h3.eventually_nhds]
        with b hb ha hz z
      have hd := ha.differentiableAt.hasFDerivAt.comp (0 : Fin g → ℂ) (hasFDerivAt_prodMk_right b (0 : Fin g → ℂ))
      have := fderiv_lift (x := fun z => e b z ≫ f) (fun z w => by simp only [(he b hb).1.1, MonObj.mul_comp])
        (he b hb).1.1 (he b hb).1.2.1 hr (he b hb).2 hd.differentiableAt
        (((Continuous.prodMk_right b).tendsto 0).eventually hz) z
      rwa [hd.fderiv] at this
    · have : DifferentiableAt ℂ (fun b : Fin m → ℂ => fderiv ℂ ζ (b, 0) ((0 : Fin m → ℂ), z)) b₁ :=
        (h2.fderiv.differentiableAt.comp b₁ (hasFDerivAt_prodMk_left b₁ (0 : Fin g → ℂ)).differentiableAt).clm_apply
          (differentiableAt_const ((0 : Fin m → ℂ), z))
      exact this
  choose! L h1 h2 using key
  refine ⟨fun b => L b b, fun b hb => (h1 b hb).self_of_nhds, fun z b₁ hb₁ => ?_⟩
  refine ((h2 b₁ hb₁ z).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hB.mem_nhds hb₁, h1 b₁ hb₁] with b hb h
  rw [linear_lift_unique (he b hb).1.1 hr (he b hb).2 (L := L b b) (L' := L b₁ b)
    fun z => ((h1 b hb).self_of_nhds z).trans (h z).symm]

theorem exists_hol_rep {O : Type} [CommRing O] {B : Set (Fin m → ℂ)} (hB : IsOpen B) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B)
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ} (hr : 0 < r)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    (act : OAct O G) :
    ∃ F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ),
      (∀ b ∈ B, ∀ a z, e b ((F b a).mulVec z) = e b z ≫ act.act a) ∧
      ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B := by
  classical
  choose L h1 h2 using fun a => haveI := act.hom a; exists_hol_linear_lift hB hr hol he hl (act.act a)
  have key : ∀ b ∈ B, ∃ F : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a, F a = LinearMap.toMatrix' (L a b) := by
    intro b hb
    have u := fun L L' => linear_lift_unique (he b hb).1.1 hr (he b hb).2 (V := Fin g → ℂ) (L := L) (L' := L')
    refine ⟨RingHom.mk' ⟨⟨fun a => LinearMap.toMatrix' (L a b), ?_⟩, fun a a' => ?_⟩ fun a a' => ?_, fun _ => rfl⟩
    · rw [u (L 1 b) LinearMap.id fun z => by rw [h1 1 b hb, act.one, Category.comp_id, LinearMap.id_apply],
        LinearMap.toMatrix'_id]
    · change LinearMap.toMatrix' (L (a * a') b) = _
      rw [u (L (a * a') b) (L a b ∘ₗ L a' b) fun z => by
        rw [h1 _ b hb, LinearMap.comp_apply, h1 _ b hb, h1 _ b hb, mul_comm, act.mul, Category.assoc],
        LinearMap.toMatrix'_comp]
    · change LinearMap.toMatrix' (L (a + a') b) = LinearMap.toMatrix' (L a b) + LinearMap.toMatrix' (L a' b)
      rw [u (L (a + a') b) (L a b + L a' b) fun z => by
        rw [h1 _ b hb, LinearMap.add_apply, (he b hb).1.1, h1 _ b hb, h1 _ b hb, act.add, MonObj.comp_mul], map_add (f := _)]
  choose F hF using key
  refine ⟨fun b => if hb : b ∈ B then F b hb else F b₀ hb₀, fun b hb a z => ?_, fun a i j => ?_⟩
  · simp only [dif_pos hb, hF, LinearMap.toMatrix'_mulVec, h1 a b hb]
  · refine (differentiableOn_pi.1 (h2 a (Pi.single j 1)) i).congr fun b hb => ?_
    simp only [dif_pos hb, hF, LinearMap.toMatrix'_apply]

def HasForm {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (P : La → (Fin g → ℂ)) : Prop :=
  ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y

open Matrix in
theorem HasForm.of_comp {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La} {P : La → (Fin g → ℂ)} {g' : ℕ}
    (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hL : Function.Injective L) (h : HasForm EF (fun x => L (P x))) :
    HasForm EF P := by
  obtain ⟨Hm, h1, h2, h3⟩ := h
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, isHermitian_mul_mul_conjTranspose _ h1, fun z hz => ?_, fun x y => ?_⟩
  · rw [key]
    exact h2 _ fun h0 => hz (hL (h0.trans (map_zero L).symm))
  · rw [key, h3]

theorem int_eq_of_exp {a b : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (a : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (b : ℂ) / k)) : a = b := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ b - a := fun k hk => by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hp := Complex.two_pi_I_ne_zero
    refine ⟨n, ?_⟩
    have : ((b : ℂ) - a) = k * n := by
      refine mul_left_cancel₀ hp ?_
      field_simp at hn
      linear_combination (2 * Real.pi * Complex.I) * hn
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((b - a).natAbs + 1) (Nat.succ_pos _)) (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem hasForm_of_weil (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt)
    (A : Out.PolAV X) (y₀ y : Sp ℂ ⟶ X) (hy : y = (𝟙_ (Over (Sp ℂ))).hom ≫ y₀)
    {e : (Fin g → ℂ) → (Over.mk y ⟶ A.A)} (he : IsExp y e) {r : ℝ} (hr : 0 < r)
    (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0)
    (hl : ∀ (n : ℕ) (x : (Fin n → ℂ) → (Over.mk y ⟶ A.A)), IsHolTo Set.univ (fun w => (x w).left) → e 0 = x 0 →
      ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), AnalyticAt ℂ ζ 0 ∧ ∀ᶠ w in 𝓝 0, e (ζ w) = x w)
    {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (P : La → (Fin g → ℂ)) (hP : ∀ a, e (P a) = 1)
    (hw : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs A.A A.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) : HasForm EF P := by
  subst hy
  obtain ⟨A', φ, hφ, -, hm, t, ht⟩ := hB _ _ y₀ A
  have hgp : IsGrpPullback A'.A A.A y₀ φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl⟩
  obtain ⟨rig, hrig⟩ := A'.rigid
  obtain ⟨u, Hm, χ, Ef, ⟨h1, h2, -⟩, -, -, -, -, -, h3, -, h4⟩ := hT A' rig hrig
  let x : (Fin A'.g → ℂ) → (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ y₀) ⟶ A.A) := fun w => Out.toBase hφ.w (u.ex w)
  have hx : ∀ z w, x (z + w) = x z * x w := fun z w => by simp only [x, u.ex_add, hm]
  have hinj : Function.Injective (fun p : 𝟙_ (Over (Sp ℂ)) ⟶ A'.A => Out.toBase hφ.w p) := fun p q h =>
    Over.OverMorphism.ext (hφ.hom_ext (congrArg (fun s => s.left) h) ((Over.w p).trans (Over.w q).symm))
  have hker : ∀ z, x z = 1 ↔ z ∈ u.Λ := fun z => by
    rw [← u.ker, ← hom_zero hx, ← hom_zero u.ex_add]
    exact hinj.eq_iff
  have hsx : Function.Surjective x := fun q => by
    obtain ⟨w, hw⟩ := u.ex_onto (Over.homMk (hφ.lift q.left (𝟙_ (Over (Sp ℂ))).hom (Over.w q)) (hφ.lift_snd _ _ _))
    refine ⟨w, Over.OverMorphism.ext ?_⟩
    change (u.ex w).left ≫ φ = _
    rw [hw]
    exact hφ.lift_fst _ _ _
  have hhol : IsHolTo Set.univ (fun w => (u.ex w).left) := fun U f => by simpa using u.hol U f
  obtain ⟨ζ, hζ, hζ'⟩ := hl _ x (isHolTo_comp_hom hhol φ) (by rw [hom_zero hx, hom_zero he.1])
  obtain ⟨L, hL⟩ := exists_linearEquiv_lift hx he.1 hsx he.2.1 (by
    haveI := u.discrete
    rw [show {z | x z = 1} = (u.Λ : Set _) from Set.ext hker]
    exact DiscreteTopology.isDiscrete) hr hk hζ.differentiableAt hζ'
  have hmem : ∀ a, L.symm (P a) ∈ u.Λ := fun a => by rw [← hker, ← hL, L.apply_symm_apply, hP]
  refine HasForm.of_comp L.symm.toLinearEquiv.toLinearMap L.symm.injective ⟨Hm, h1, h2, fun a a₂ => ?_⟩
  refine (h3 ⟨_, hmem a⟩ ⟨_, hmem a₂⟩).symm.trans (congrArg _ (int_eq_of_exp fun k hk0 => ?_))
  have e1 := h4 k ⟨_, hmem a⟩ ⟨_, hmem a₂⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have e2 := hw k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have hp : ∀ a, (e ((k : ℂ)⁻¹ • P a)).left = (u.ex ((k : ℂ)⁻¹ • L.symm (P a))).left ≫ φ := fun a => by
    rw [← map_smul, ← L.apply_symm_apply ((k : ℂ)⁻¹ • P a), hL, L.symm_apply_apply]
    rfl
  haveI := A.isAb.comm
  have e3 := (weilIs_grpPullback_of_comm _ _ A.A A'.A y₀ φ A.L A'.L A.isLB A'.isLB hgp (LBIso.symm ⟨t, ht⟩) _ k _ _ _ _ _ (hp a) (hp a₂)).1 e1
  exact congrArg Units.val (weilIs_unique_fieldPoint _ A.A A.L A.isLB ℂ _ k _ _ _ _ e3 e2)

end

end GlobalTheory.LocLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOActDescendOfEtaleIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

theorem exists_oAct_descend_of_etale_isogeny :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (a : OAct O A), IsAbelianScheme A → IsAbelianScheme B → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A) (c : O), x ≫ ψ = 1 → (x ≫ a.act c) ≫ ψ = 1) → ∃ b : OAct O B, ∀ c, a.act c ≫ ψ = ψ ≫ b.act c := by
  intro O _ S _ A B _ _ _ _ ψ a hA hB hψ hf he hs hker
  have hsep : IsSeparated B.hom := by
    have := hB.proper
    infer_instance
  have key : ∀ c : O, ∃ g' : B ⟶ B, IsMonHom g' ∧ ψ ≫ g' = a.act c ≫ ψ ∧
      ∀ g'' : B ⟶ B, ψ ≫ g'' = a.act c ≫ ψ → g'' = g' := by
    intro c
    have := a.hom c
    refine _root_.GlobalTheory.HkFactor.exists_unique_factor S A B B ψ (a.act c ≫ ψ) hA hB hsep hψ hf he hs inferInstance ?_
    intro k _ _ t x hx
    rw [← Category.assoc]
    exact hker k t x c hx
  choose f hf1 hf2 hf3 using key
  refine ⟨⟨f, hf1, ?_, ?_, ?_⟩, fun c => (hf2 c).symm⟩
  · refine (hf3 1 _ ?_).symm
    rw [a.one, Category.id_comp, Category.comp_id]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [← Category.assoc, hf2, Category.assoc, hf2, a.mul, Category.assoc]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [MonObj.comp_mul, hf2, hf2, a.add]
    exact (map_mul (IsMonHom.monoidHom ψ A) _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistPullMulFn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_mulPull_gen_over (H : Out.MulPullSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    (T : Over S) (N : ℕ) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ N).left] ![(N : ℤ) ^ 2, -1]),
      α.IsGen := by
  obtain ⟨α₀, hα₀⟩ := H _ P N
  have e₁ : (snd T P.A).left ≫ (Out.mulA P.A N).left = (snd T P.A ^ N).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, (snd T P.A ^ N).left])
    (ε' := ![(N : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((N : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (Out.mulA P.A N).left] ![(N : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα⟩

theorem exists_twistPull_mul_fn : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (θ : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (th : LB.Sec (Out.LPow P.A P.L 1 T)), u.IsAH Hm χ → Odd N → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L 1 T).U j) (th.f j) = θ z * u.fr (j 0) z ^ (1 : ℤ)) → ∃ (s1 : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)) (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ N).left] ![(N : ℤ) ^ 2, -1])) (c : ℂ), c ≠ 0 ∧ α.IsGen ∧ Out.IsTwistPull P.A P.L (Out.mulT P.A T N) (snd T P.A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α th s1 ∧ (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s1.f j) = c * θ ((N : ℂ) • z) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  intro hLaw _ _ _ P u Hm χ N θ T _ p th hAH _ hth
  have hL := P.isLB
  obtain ⟨α, hα⟩ := exists_mulPull_gen_over hLaw.mulPull P T N
  obtain ⟨s1, hs1⟩ := ThetaPtExist.exists_isTwistPull hL (Out.mulT P.A T N) (snd T P.A ^ N) (lift_snd _ _)
    ((N : ℤ) ^ 2) 1 α hα th
  obtain ⟨c, hc0, -, hc, -⟩ := (ThetaFn.pull_analytic_at hL hAH (ψ := Out.mulT P.A T N) (p := p)
    (m := snd T P.A ^ N) (lift_snd _ _) (Φ := (N : ℂ) • LinearMap.id) (fun z => by
      rw [LinearMap.smul_apply, LinearMap.id_apply, ThetaFn.exAt_mulT]) (a := (N : ℤ) ^ 2) (b := 1) hα).2
  have h1 : ThetaFn.IsFnAt u p 1 th θ := fun j z hj =>
    hth j z ((ThetaFn.exAt_mem_chart_iff u p 1 j z).1 hj)
  have h2 := ThetaFn.isFnAt_fnAt u p hL ((N : ℤ) ^ 2) s1
  refine ⟨s1, α, c, hc0, hα, hs1, fun j z hj => ?_⟩
  refine (h2 j z ((ThetaFn.exAt_mem_chart_iff u p _ j z).2 hj)).trans ?_
  rw [hc th s1 θ _ hs1 h1 h2 z]
  rfl

end GlobalTheory
end

