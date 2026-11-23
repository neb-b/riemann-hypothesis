module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelAutActsOnRaisedModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.MulAmple

open GlobalTheory.MulPull GlobalTheory.MulFinite TopologicalSpace

theorem gs_sec_trans {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (p : Z ⟶ X) (z : Z) {k k' : H.ι}
    (hk : p z ∈ H.U k) (hk' : p z ∈ H.U k') :
    gs p z (H.U k) (s.f k) =
      (gm p z (H.U k ⊓ H.U k') (H.g k k')).val * gs p z (H.U k') (s.f k') := by
  have hm : p z ∈ H.U k ⊓ H.U k' := ⟨hk, hk'⟩
  exact (gs_res p z _ hm _).symm.trans ((congrArg (gs p z _) (s.compat k k')).trans
    ((gs_mul p z _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit p z _ hm _) (gs_res p z _ hm _))))

theorem isUnit_gs_sec {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (p : Z ⟶ X) (z : Z) {k : H.ι}
    (hk : p z ∈ H.U k) : IsUnit (gs p z (H.U k) (s.f k)) ↔ p z ∈ Out.nonzeroLocus s := by
  refine ⟨fun h => Opens.mem_iSup.2 ⟨k, (isUnit_gs p z _ hk _).1 h⟩, fun h => ?_⟩
  obtain ⟨k', hk'⟩ := Opens.mem_iSup.1 h
  have h' : p z ∈ H.U k' := X.basicOpen_le _ hk'
  rw [gs_sec_trans s p z hk h']
  exact (Units.isUnit _).mul ((isUnit_gs p z _ h' _).2 hk')

theorem units_mul_pow_mul_inv_cancel {R : Type} [CommRing R] (g h t : Rˣ) (x y : R) (a b : ℕ) :
    (g.val * x) ^ a * (h.val * y) ^ b * ((g ^ a * h ^ b * t)⁻¹).val = x ^ a * y ^ b * (t⁻¹).val := by
  have e : g ^ a * h ^ b * (g ^ a * h ^ b * t)⁻¹ = t⁻¹ := by
    rw [mul_inv, mul_inv_cancel_left]
  have e' : g.val ^ a * h.val ^ b * ((g ^ a * h ^ b * t)⁻¹).val = (t⁻¹).val := congrArg Units.val e
  rw [← e']; ring

theorem exists_fn₂ {X Z : Scheme.{0}} {H : LB X} (hH : H.IsLB) (p q : Z ⟶ X) (a b : ℕ) (ha : a ≠ 0)
    (hb : b ≠ 0) (h : HasGen H (K := Fin 2) ![p, q] ![(a : ℤ), (b : ℤ)]) (s s' : LB.Sec H) :
    ∃ c : Γ(Z, ⊤), Z.basicOpen c = p ⁻¹ᵁ Out.nonzeroLocus s ⊓ q ⁻¹ᵁ Out.nonzeroLocus s' := by
  obtain ⟨α, hα⟩ := h
  let V : (Fin 2 → H.ι) → Z.Opens := fun j => LB.wchart H (K := Fin 2) ![p, q] j
  have l₁ : ∀ j, V j ≤ p ⁻¹ᵁ H.U (j 0) := fun j z hz => Set.mem_iInter.1 hz 0
  have l₂ : ∀ j, V j ≤ q ⁻¹ᵁ H.U (j 1) := fun j z hz => Set.mem_iInter.1 hz 1
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs p z (H.U (j 0)) (s.f (j 0)) ^ a * gs q z (H.U (j 1)) (s'.f (j 1)) ^ b *
        ((gm (𝟙 Z) z (V j) (α.s j))⁻¹).val := by
    refine ⟨fun j => (p.appLE _ _ (l₁ j)).hom (s.f (j 0)) ^ a *
      (q.appLE _ _ (l₂ j)).hom (s'.f (j 1)) ^ b * (show Γ(Z, V j) from ((α.s j)⁻¹).val), fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·)
      ((gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))) ?_)
    · exact congrArg (· ^ a) (gs_appLE p z _ _ _ hz _)
    · exact congrArg (· ^ b) (gs_appLE q z _ _ _ hz _)
    · exact (gs_unit (𝟙 Z) z _ hz _).trans (congrArg Units.val (map_inv _ _))
  have hex : ∀ z : Z, ∃ j, z ∈ V j := fun z => by
    obtain ⟨k, hk⟩ := exists_chart hH (p z)
    obtain ⟨l, hl⟩ := exists_chart hH (q z)
    refine ⟨![k, l], Set.mem_iInter.2 fun i => ?_⟩
    fin_cases i
    · exact hk
    · exact hl
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => Opens.mem_iSup.2 (hex z)
  obtain ⟨c, hc, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans
        (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      have e := gen_trans hα (𝟙 Z) z (j := j) (j' := j') hz.1 hz.2
      have t : trF (L := H) (K := Fin 2) ![p, q] ![(a : ℤ), (b : ℤ)] (𝟙 Z) z j j' =
          gm p z (H.U (j 0) ⊓ H.U (j' 0)) (H.g (j 0) (j' 0)) ^ a *
            gm q z (H.U (j 1) ⊓ H.U (j' 1)) (H.g (j 1) (j' 1)) ^ b := by
        rw [trF, Fin.prod_univ_two, ← zpow_natCast, ← zpow_natCast]
        rfl
      rw [t] at e
      rw [hu j z hz.1, hu j' z hz.2, gs_sec_trans s p z (l₁ j hz.1) (l₁ j' hz.2),
        gs_sec_trans s' q z (l₂ j hz.1) (l₂ j' hz.2)]
      exact (congrArg (fun w : (Z.presheaf.stalk z)ˣ => _ * (w⁻¹).val) e).trans
        (units_mul_pow_mul_inv_cancel _ _ _ _ _ a b))
  refine ⟨c, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := hex z
  have k₁ : gs (𝟙 Z) z ⊤ c = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj c).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (hc j))
  refine (isUnit_gs (𝟙 Z) z ⊤ trivial c).symm.trans ?_
  rw [k₁, hu j z hj, Units.isUnit_mul_units, IsUnit.mul_iff, isUnit_pow_iff ha, isUnit_pow_iff hb,
    isUnit_gs_sec s p z (l₁ j hj), isUnit_gs_sec s' q z (l₂ j hj)]
  rfl

theorem hasGen_of_chart {X Z : Scheme.{0}} {H : LB X} (hH : H.IsLB) (p : Z ⟶ X) (j₀ : H.ι)
    (h : ∀ z, p z ∈ H.U j₀) : HasGen H (K := Fin 1) ![p] ![1] := by
  have le : ∀ j : Fin 1 → H.ι, LB.wchart H (K := Fin 1) ![p] j ≤ p ⁻¹ᵁ (H.U (j 0) ⊓ H.U j₀) :=
    fun j z hz => ⟨Set.mem_iInter.1 hz 0, h z⟩
  refine ⟨⟨fun j => res (le j) (pullU p _ (H.g (j 0) j₀))⟩, fun j j' => unit_ext fun z hz => ?_⟩
  have v : ∀ j : Fin 1 → H.ι, z ∈ LB.wchart H (K := Fin 1) ![p] j →
      gm (𝟙 Z) z _ (res (le j) (pullU p _ (H.g (j 0) j₀))) =
        gm (𝟙 Z ≫ p) z (H.U (j 0) ⊓ H.U j₀) (H.g (j 0) j₀) := fun j hj =>
    (gm_res (𝟙 Z) z (le j) hj _).trans (gm_pull (𝟙 Z) p z _ (le j hj) _)
  refine ((gm_res (𝟙 Z) z _ hz _).trans (v j hz.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_linComb H ![p] ![1] (𝟙 Z) z j j' hz.1 hz.2)
    ((gm_res (𝟙 Z) z _ hz _).trans (v j' hz.2))).trans ?_)
  rw [Fin.prod_univ_one]
  change gm (𝟙 Z ≫ p) z (H.U (j 0) ⊓ H.U (j' 0)) (H.g (j 0) (j' 0)) ^ (1 : ℤ) * _ = _
  rw [zpow_one]
  exact gm_cocycle hH (𝟙 Z ≫ p) z (le j hz.1).1 (le j' hz.2).1 (h z)

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem hasGen_pow₂ (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε) {T : Over S} (x : T ⟶ A)
    (hone : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1]) (n : ℕ) :
    HasGen L (K := Fin 3) ![x.left, (x⁻¹).left, (x ^ n).left]
      ![(n : ℤ) ^ 2 + n, (n : ℤ) ^ 2 - n, -2] := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact (hone.inv.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, zpow_ofNat, sq])
  | one =>
    exact (hone.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, zpow_ofNat])
  | more n ih₀ ih₁ =>
    have hc := hcube.pull (lift (x ^ (n + 1)) (lift x x⁻¹)).left
    refine ((hc.mul hc).mul ((ih₁.mul ih₁).mul (ih₀.inv.mul
      ((hone.mul hone).mul (hone.mul hone))))).of_formEq hL (fun U _ h => ?_)
    refine ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
        (prod_cub (x ^ (n + 1)) x x⁻¹ h) (prod_cub (x ^ (n + 1)) x x⁻¹ h))) rfl)).trans ?_
    have e₁ : x ^ (n + 1) * x * x⁻¹ = x ^ (n + 1) := mul_inv_cancel_right _ _
    have e₂ : x ^ (n + 1) * x = x ^ (n + 2) := (pow_succ x (n + 1)).symm
    have e₃ : x ^ (n + 1) * x⁻¹ = x ^ n := by rw [pow_succ, mul_inv_cancel_right]
    rw [e₁, e₂, e₃, mul_inv_cancel]
    apply Additive.ofMul.injective
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ,
      Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv,
      ofMul_zpow, ofMul_one]
    push_cast
    module

theorem isFinite_pow [IsProper A.hom] [IsAffine S] (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε)
    {I : Type} (s : I → LB.Sec L) (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (hs : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i))) (n : ℕ) (hn : 1 ≤ n) :
    IsFinite ((𝟙 A) ^ n : A ⟶ A).left := by
  rcases hn.eq_or_lt with rfl | hn
  · rw [pow_one, Over.id_left]; infer_instance
  generalize hm : ((𝟙 A) ^ n : A ⟶ A) = m
  have hw : m.left ≫ A.hom = A.hom := Over.w m
  have : IsProper (m.left ≫ A.hom) := by rw [hw]; infer_instance
  have : IsProper m.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite m.left from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  have hy : ∀ z, m.left (m.left.fiberι y z) = y := fun z =>
    (m.left.range_fiberι y).le ⟨z, rfl⟩
  let T : Over S := Over.mk (m.left.fiberι y ≫ A.hom)
  let x : T ⟶ A := Over.homMk (m.left.fiberι y) rfl
  have hxm : x ^ n = x ≫ m := by rw [← hm, MonObj.comp_pow, Category.comp_id]
  have hxi : x⁻¹ = x ≫ GrpObj.inv := rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart hL y
  obtain ⟨j₁, hj₁⟩ := exists_chart hL ((1 : A ⟶ A).left y)
  have h₀ : HasGen L (K := Fin 1) ![(x ^ n).left] ![1] := hasGen_of_chart hL _ j₀ fun z => by
    rw [hxm]
    exact (congrArg (· ∈ L.U j₀) (hy z)).mpr hj₀
  have h₁ : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1] := hasGen_of_chart hL _ j₁ fun z => by
    have e : (1 : T ⟶ A) = x ≫ m ≫ (1 : A ⟶ A) := by rw [MonObj.comp_one, MonObj.comp_one]
    rw [e]
    exact (congrArg (fun w => (1 : A ⟶ A).left w ∈ L.U j₁) (hy z)).mpr hj₁
  have hle : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  have h₂ : HasGen L (K := Fin 2) ![x.left, (x⁻¹).left]
      ![((n ^ 2 + n : ℕ) : ℤ), ((n ^ 2 - n : ℕ) : ℤ)] :=
    ((hasGen_pow₂ hL hcube x h₁ n).mul (h₀.mul h₀)).of_formEq hL fun U _ h => by
      apply Additive.ofMul.injective
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ,
        Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul,
        ofMul_zpow, ofMul_one]
      push_cast [hle]
      module
  have key := fun i : I × I => exists_fn₂ hL x.left (x⁻¹).left _ _ (by positivity)
    (by have : n < n ^ 2 := by nlinarith
        omega) h₂ (s i.1) (s i.2)
  choose c hc using key
  have := isAffineHom_fromSpecResidueField A.left y
  have hx : IsAffineHom x.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)).flip this
  have : IsIso (GrpObj.inv : A ⟶ A).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.inv : A ⟶ A)))
  have hx' : IsAffineHom (x⁻¹).left := by
    rw [hxi, Over.comp_left]; infer_instance
  have hp : IsProper (m.left.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd m.left (A.left.fromSpecResidueField y)))
  have hsep : T.left.IsSeparated := by
    have : IsSeparated (m.left.fiberToSpecResidueField y ≫ terminal.from _) := inferInstance
    rw [terminal.comp_from] at this
    exact ⟨this⟩
  refine locallyQuasiFinite_of_cover (K := A.left.residueField y)
    (m.left.fiberToSpecResidueField y) c ?_ fun i => ?_
  · refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (x.left z)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ ((x⁻¹).left z)))
    exact Opens.mem_iSup.2 ⟨(i, j), (hc (i, j)).ge ⟨hi, hj⟩⟩
  · refine (congrArg IsAffineOpen (hc i)).mpr ?_
    exact ((hs i.1).preimage x.left).inf ((hs i.2).preimage (x⁻¹).left)

end

theorem finite_flat_surjective_pow :
    Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ n : ℕ, 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left ∧ Flat ((𝟙 A) ^ n : A ⟶ A).left ∧ Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  intro hl R _ A _ _ hA M hM hamp n hn
  obtain ⟨d, -, m, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A M hM).1 hamp
  have hH := isLB_pw hM d
  have := hA.proper
  have := hA.smooth
  have hcube : HasGen (pw M d) (thφ A (x3 A)) thε :=
    GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hl R A hA ⟨_, hH, m, s, hs⟩ _ hH
  have hf := isFinite_pow hH hcube s hs.1 (fun i => (hs.2 i).1) n hn
  have hm : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := MulN.isMonHom_mulA A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R),
      Flat ((Over.pullback t).map ((𝟙 A) ^ n : A ⟶ A)).left ∧
        Surjective ((Over.pullback t).map ((𝟙 A) ^ n : A ⟶ A)).left := fun K _ _ t =>
    flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (Out.TLinPf.isAb_pullback t A hA) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (MulN.isPullback_baseChange t _) hf)
  exact ⟨hf, flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ A A _ inferInstance
    inferInstance inferInstance hf fun K _ _ t => (hgeo K t).1,
    MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2⟩

end GlobalTheory.MulAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem System.levelStructureConditions_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hpq hlev S p W hp hW i
  obtain ⟨l₀, h, hR⟩ := S.raises p W hp hW i
  have hdvd : l₀.Dvd i.l := ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 i.l l₀ h).1
  obtain ⟨hded, hunit, -⟩ := (GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW
  have hgood : Good (S.Y p W hp hW i).t := by
    obtain ⟨b, r, ν, -, -, ⟨A⟩⟩ := hR
    exact good_pullback L3.gtBaseChange E H _ _ _ _ A.π A.mu (S.B (S.ch p) l₀ h.1).good
  refine ⟨⟨?_, fun hA => ?_, ?_, ?_, ?_, ?_⟩, hgood.2.1⟩
  · exact _root_.GlobalTheory.LevActs.levelActs_of_raises L1 L2 L3 E H D Xo _ _ _ hpq l₀ _ i.l i.c _ _ _ hdvd hded hR
  · exact GlobalTheory.T.raised_model_level_one_descends L1 L2 L3 E H D Xo _ _ _ hlev l₀ _ i.l i.c _ _ _ (S.aux _).1.pos hdvd hA hded hR
  · exact _root_.GlobalTheory.PushInv.pushInvertible_of_model L1 L2 L3 E H D i.l _ _ _ _ _ _ (S.Y p W hp hW i).oF _ _ (ofModel (S.Y p W hp hW i)) hded
      hgood.2.2
  · obtain ⟨U, hU, hσ⟩ := GlobalTheory.torsion_section_extends_abLocus E H D i.l _ i.c _ _ (S.Y p W hp hW i) hded hgood.1
    exact ⟨U, hU, fun a n hn => ⟨hσ _ n (hunit n hn), hσ _ n (hunit n hn)⟩⟩
  · intro V K _ _ _ _ _ _ _
    exact GlobalTheory.goodRedExt_of_isDiscreteValuationRing hext E H D i.l _ i.c _ _ _ V K
  · intro V C _ _ _ _ _ _ _ hV _
    exact GlobalTheory.GoodRedUnitBall.goodRedExt_unitBall hext E H D Xo _ _ _ l₀ _ i.l i.c _ _ _ hR V C hV

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFrom

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have hc : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    simp
  exact hf.countable

theorem fromC_of_isPEL : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (τ : SAB H S), IsPEL D a bas ρ t τ → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (PELClass (b := b) D a bas ρ em) t x := by
  intro hL _ E _ _ _ H D g J _ a w w' bas _ _ _ _ hcl N' o _ b em ρ _ hb S s t τ hτ K _ _ x
  obtain ⟨β', hβ'⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨β, hβ⟩ : ∃ β : o →+* K, x ≫ s = spMap β := ⟨β'.hom, hβ'.symm⟩
  obtain ⟨tx, htx⟩ := _root_.GlobalTheory.tObj_pull o g (N' ^ 2) J b S (Sp K) s (spMap β) x t hβ
  obtain ⟨τx, hτx⟩ := GlobalTheory.PELPull.isPEL_pull E H D g (N' ^ 2) J a bas o b ρ S (Sp K) s (spMap β) x t tx τ hβ htx hτ
  obtain ⟨K₀, β₀, t₀, hβ₀, hcount, -, ht₀⟩ := _root_.GlobalTheory.ThetaDescent.descends_to_fg_subfield o g (N' ^ 2) J b K β tx
  haveI : Countable K₀ := hcount (countable_of_finiteType o hb.2.1)
  have hcomp : spMap β = spMap K₀.subtype ≫ spMap β₀ := by
    rw [← hβ₀, ← Spec.map_comp]; rfl
  obtain ⟨τ₀, hτ₀⟩ := _root_.GlobalTheory.PELDesc.isPEL_descends hL E H D g (N' ^ 2) J a bas o b ρ K₀ K K₀.subtype β₀ (spMap β) t₀ tx τx
    hcl hcomp ht₀ hτx
  obtain ⟨-, j, hj⟩ := _root_.GlobalTheory.exists_ringHom_complex_comp_eq_of_countable o em K₀ β₀ hb.1 hb.2.1 hb.2.2
  have hjc : spMap j ≫ spMap β₀ = spMap em := by
    rw [← hj, ← Spec.map_comp]; rfl
  obtain ⟨tc, htc⟩ := _root_.GlobalTheory.tObj_pull o g (N' ^ 2) J b (Sp K₀) (Sp ℂ) (spMap β₀) (spMap em) (spMap j) t₀ hjc
  have hc := GlobalTheory.PELPull.isPEL_pull E H D g (N' ^ 2) J a bas o b ρ (Sp K₀) (Sp ℂ) (spMap β₀) (spMap em) (spMap j)
    t₀ tc τ₀ hjc htc hτ₀
  unfold FromC
  rw [hβ]
  exact ⟨K₀, inferInstance, β₀, K₀.subtype, j, t₀, tx, tc, hj, hcomp, htx, ht₀, htc, hc⟩

end GlobalTheory.PELFrom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

theorem pw_pw_natCast {X : Scheme.{0}} (H : LB X) (a b : ℕ) :
    pw (pw H a) b = pw H ((a * b : ℕ) : ℤ) := by
  rw [Nat.cast_mul]
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem triv_theta_pull {S S' : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (g : S' ⟶ S)
    (H : LB A.left) (h : Triv (Theta ((Over.pullback g).obj A) (H.pull (pullback.fst A.hom g)))) :
    Triv ((Theta A H).pull (pullback.fst (G3 A).hom g)) := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨u, hu⟩ := GlobalTheory.CubeDescent.exists_gen_comp H (pullback.fst A.hom g) _ _ t ht
  let B := (Over.pullback g).obj A
  let T : Over S' := Over.mk (pullback.snd (G3 A).hom g)
  have hG := isGrpPullback_pullback A g
  let y : Fin 3 → (T ⟶ B) := fun i => Over.homMk
    (pullback.lift (pullback.fst (G3 A).hom g ≫ (x3 A i).left) (pullback.snd (G3 A).hom g)
      (by rw [Category.assoc, Over.w, pullback.condition])) (pullback.lift_snd _ _ _)
  let r : T ⟶ G3 B := lift (y 0) (lift (y 1) (y 2))
  have hr : ∀ i, r ≫ x3 B i = y i := fun i => by fin_cases i <;> simp [r, x3]
  let U : Over.mk (T.hom ≫ g) ⟶ G3 A := Over.homMk (pullback.fst (G3 A).hom g) pullback.condition
  have key : ∀ I : Finset (Fin 3), r.left ≫ (psum B (x3 B) I).left ≫ pullback.fst A.hom g =
      pullback.fst (G3 A).hom g ≫ (psum A (x3 A) I).left := fun I => by
    have e₁ : r ≫ psum B (x3 B) I = psum B y I :=
      (psum_hom (preHom r) (x3 B) I).trans (congrArg (fun z => psum B z I) (funext hr))
    have e₂ := psum_push hG y (x3 A) U (fun i => Over.OverMorphism.ext (pullback.lift_fst _ _ _)) I
    rw [← Category.assoc, ← Over.comp_left, e₁]
    exact e₂
  refine (CubeGen.triv_pull_iff H (thφ A (x3 A)) thε _).2 ?_
  have e : (fun k => pullback.fst (G3 A).hom g ≫ thφ A (x3 A) k) =
      fun k => r.left ≫ thφ B (x3 B) k ≫ pullback.fst A.hom g := funext fun k => (key k.down).symm
  unfold CubeGen.TrivAt
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ u hu r.left⟩

theorem exists_ne_zero {X : Scheme.{0}} [Nonempty X] {N : LB X} {I : Type} (s : I → LB.Sec N)
    (h : ⨆ i, Out.nonzeroLocus (s i) = ⊤) : ∃ (σ : LB.Sec N) (k : N.ι), σ.f k ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [h]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  refine ⟨s i, k, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hk
  exact hk

theorem relAmple_of_fibres : Out.Laws → ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap O K)))) (M.pull (pullback.fst A.hom (spMap (algebraMap O K)))) → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (IsLocalRing.residue O)))) (M.pull (pullback.fst A.hom (spMap (IsLocalRing.residue O)))) → Out.RelAmple A M := by
  intro hL O K _ _ _ _ _ _ _ _ A _ hA M hM hK hk
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hB := CubeGen.isAb_baseChange hA (spMap (algebraMap O K))
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K _ _ (LB.isLB_pull hM _)).1 hK
  have hH := isLB_pw hM d
  have hproj : IsProjBy ((Over.pullback (spMap (algebraMap O K))).obj A).hom :=
    ⟨_, isLB_pw (LB.isLB_pull hM _) _, n, s, hs⟩
  have cK := triv_theta_pull A _ (pw M d)
    (_root_.GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hL K _ hB hproj _ (LB.isLB_pull hH (pullback.fst A.hom (spMap (algebraMap O K)))))
  have s₂ : Smooth (A ⊗ A).hom := by
    change Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have p₂ : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have c₂ : GeometricallyConnected (A ⊗ A).hom := by
    change GeometricallyConnected (pullback.fst A.hom A.hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have s₃ : Smooth (G3 A).hom := by
    change Smooth (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have p₃ : IsProper (G3 A).hom := by
    change IsProper (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have c₃ : GeometricallyConnected (G3 A).hom := by
    change GeometricallyConnected (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have cube : Triv (Theta A (pw M d)) :=
    _root_.GlobalTheory.ValGenExtend.triv_of_triv_generic O K _ _ (G3 A).hom _ _ (IsPullback.of_hasPullback _ _) s₃ inferInstance (gi _ _ _ s₃ c₃) _
      (LB.isLB_linComb hH _ _) cK
  have ne : Nonempty ((Over.pullback (spMap (algebraMap O K))).obj A).left :=
    ⟨(η[(Over.pullback (spMap (algebraMap O K))).obj A]).left (default : PrimeSpectrum K)⟩
  have hσ : ∃ (σ : LB.Sec ((pw M d).pull (pullback.fst A.hom (spMap (algebraMap O K))))) (k : _), σ.f k ≠ 0 := by
    have := @exists_ne_zero _ ne _ _ s hs.1
    rw [GlobalTheory.TrivLocus.pull_pw]
    exact this
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨-, t, -, -, ht⟩ := _root_.GlobalTheory.exists_smul_sec_nonzero_on_special_fibre O K _ _ A.hom _ _ (IsPullback.of_hasPullback _ _) hA.smooth
    inferInstance (gi _ _ _ hA.smooth hA.geomConnected) _ hH σ hσ
  have hu := _root_.GlobalTheory.SquareGenerated.exists_secs_sq_generate O K A hA _ hH cube t ht
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, pw_pw_natCast] at hu
  obtain ⟨m, u, hu⟩ := hu
  have aff := _root_.GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres O _ A.hom M (d * 2) m u (by omega) hA.proper hM hu (fun q hq => by
    by_cases h0 : q = ⊥
    · exact ⟨K, inferInstance, algebraMap O K,
        h0 ▸ (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K), hK⟩
    · exact ⟨_, inferInstance, IsLocalRing.residue O,
        IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal (hq.isMaximal h0)).symm, hk⟩)
  obtain ⟨e, he, hv⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw_of_affine_loci O _ A.hom _ m u (isLB_pw hM _) hu aff
  rw [pw_pw_natCast] at hv
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy O A M hM).2 ⟨d * 2 * e, Nat.mul_pos (by omega) he, hv⟩

end GlobalTheory.FibreAmple
end

