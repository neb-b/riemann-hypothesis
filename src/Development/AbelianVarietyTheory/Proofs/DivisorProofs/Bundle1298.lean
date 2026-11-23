module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolUnifEnd


open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel in
theorem exists_pow_eq_one_of_surjective (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (ψ : A ⟶ B) [IsMonHom ψ] [Surjective ψ.left] :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = 1 → x ^ n = 1 := by
  have := hB.proper
  have := hA.proper
  have := hA.comm
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProper (ψ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left B.hom
  have hA' : SmoothOfRelativeDimension g (ψ.left ≫ B.hom) := by rw [Over.w]; exact hgA
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint B.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left B.hom hgB hA' (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main ℂ Z hZ inferInstance
  refine ⟨N, hN, fun x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem exists_factor_pow (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A)
    [IsSeparated A'.hom] [LocallyOfFiniteType A'.hom] (N : ℕ) (hN : 1 ≤ N) (φ : A ⟶ A') [IsMonHom φ]
    (h : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → y ≫ φ = 1) :
    ∃ α : A ⟶ A', IsMonHom α ∧ (𝟙 A ^ N) ≫ α = φ := by
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨hmon, hfin, het, hsurj⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hA hunit
  have key : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ (𝟙 A ^ N) = 1 → x ≫ φ = 1 := by
    intro T x hx
    let K := pullback (𝟙 A ^ N) η[A]
    let inc : K ⟶ A := pullback.fst ((𝟙 A ^ N)) η[A]
    have hinc : inc ≫ (𝟙 A ^ N) = 1 := by
      rw [pullback.condition, toUnit_unique (pullback.snd ((𝟙 A ^ N)) η[A]) (toUnit K)]; rfl
    have hp := (IsPullback.of_hasPullback ((𝟙 A ^ N)) η[A]).map (Over.forget (Sp ℂ))
    have he : Etale (pullback.snd ((𝟙 A ^ N)) η[A]).left :=
      MorphismProperty.of_isPullback (P := @Etale) hp het
    have hw : (pullback.snd ((𝟙 A ^ N)) η[A]).left = K.hom := by
      simpa using Over.w (pullback.snd ((𝟙 A ^ N)) η[A])
    rw [hw] at he
    have : IsReduced K.left := GlobalTheory.isReduced_of_smooth_of_isReduced K.hom
    have hk : inc ≫ φ = 1 := by
      refine Over.OverMorphism.ext ?_
      have : LocallyOfFiniteType ((inc ≫ φ).left ≫ A'.hom) := by rw [Over.w]; infer_instance
      refine ext_of_apply_eq A'.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
        ((Over.w _).trans (Over.w _).symm)
      let p : Over.mk (𝟙 (Sp ℂ)) ⟶ K :=
        Over.homMk (pointOfClosedPoint K.hom z hz) (pointOfClosedPoint_comp _ _ _)
      have hpN : (p ≫ inc) ^ N = 1 := by
        have : (p ≫ inc) ^ N = (p ≫ inc) ≫ (𝟙 A ^ N) := by rw [MonObj.comp_pow, Category.comp_id]
        rw [this, Category.assoc, hinc, MonObj.comp_one]
      have e : p ≫ inc ≫ φ = p ≫ 1 := by
        rw [MonObj.comp_one, ← Category.assoc]
        exact h _ hpN
      have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) e
      have hz' : p.left (IsLocalRing.closedPoint ℂ) = z := pointOfClosedPoint_apply K.hom z hz _
      simp only [Over.comp_left] at e'
      rw [← hz']
      exact e'
    have hx' : x ≫ (𝟙 A ^ N) = toUnit T ≫ η[A] := hx
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ φ = 1
    rw [hk, MonObj.comp_one]
  obtain ⟨⟨α, hα, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A A A' ((𝟙 A ^ N)) φ hmon
    inferInstance inferInstance hsurj inferInstance key
  exact ⟨α, hα, hc⟩

theorem exists_isMonHom_of_map_lattice :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x ∈ u.Λ, M x ∈ u.Λ) → ∃ α : A ⟶ A, IsMonHom α ∧ ∀ w, u.ex (M w) = u.ex w ≫ α := by
  intro A _ g hA hgA L u M hM
  obtain ⟨hL, -⟩ := abelianSchemeLaws_all
  obtain ⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩ :=
    SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA
  obtain ⟨Q, i', r', -, hi', hr', hir'⟩ :=
    EighthPowerFactor.exists_polAV_hypS_retract ℂ B g hB hgB MB hMB hamp hK
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -, -, -, -, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  have hu := TorusTransfer.tangent_bijective u hgA
  haveI := hi; haveI := hr; haveI := hi'; haveI := hr'
  obtain ⟨J, hJ, hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v
    hv1 hv2 (i ≫ i') inferInstance
  obtain ⟨R, hR, hRΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A A Q.isAb hA Q.L L Q.g g v u
    hu.1 hu.2 (r' ≫ r) inferInstance

  have hunit : IsUnit ((m : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (m : ℂ) (by exact_mod_cast (show m ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  have hsB := (abelianScheme_id_pow_finite_etale_surjective _ B m hB hunit).2.2.2
  have : Surjective (r.left ≫ i.left) := by rw [← Over.comp_left, hri]; exact hsB
  have : Surjective i.left := Surjective.of_comp r.left i.left
  obtain ⟨n, hn, hkill⟩ := exists_pow_eq_one_of_surjective A B g hA hB hgA hgB i

  have hpt : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ (i ≫ i') ≫ (r' ≫ r) ≫ (i ≫ i') = (x ≫ i ≫ i') ^ m := by
    intro x
    simp only [Category.assoc]
    rw [reassoc_of% hir', reassoc_of% hri, ← Category.assoc x i, ← Category.assoc (x ≫ i), MonObj.comp_pow,
      Category.comp_id, MonObj.pow_comp, Category.assoc]
  have hsubv : ∀ a b, v.ex a = v.ex b → a - b ∈ v.Λ := by
    intro a b h
    rw [← v.ker]
    have e := v.ex_add (a - b) b
    rw [sub_add_cancel, h] at e
    have e2 := congrArg (· * (v.ex b)⁻¹) e
    simpa using e2.symm
  have hRJ : ∀ z, R (J z) = m • z := by
    intro z
    have hJy : ∀ t : ℂ, J (t • (R (J z) - m • z)) ∈ v.Λ := by
      intro t
      have h1 : v.ex (J (R (J (t • z)))) = v.ex (m • J (t • z)) := by
        rw [hJ, hR, hJ, holUnif_ex_nsmul_eq_pow, hJ, ← hpt]
        simp only [Category.assoc]
      have h2 := hsubv _ _ h1
      have h3 : t • (R (J z) - m • z) = R (J (t • z)) - m • (t • z) := by
        rw [map_smul, map_smul, smul_sub, smul_comm t m z]
      rw [h3, map_sub, map_nsmul]
      exact h2
    have hJy0 : J (R (J z) - m • z) = 0 :=
      LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by rw [← map_smul]; exact hJy t
    have hker : ∀ t : ℂ, u.ex (t • (R (J z) - m • z)) ≫ i = 1 := by
      intro t
      have h2 : u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' = 1 := by
        rw [← hJ, map_smul, hJy0, smul_zero, holUnif_ex_zero_eq_one]
      calc u.ex (t • (R (J z) - m • z)) ≫ i = u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' ≫ r' := by
            rw [hir', Category.comp_id]
        _ = (u.ex (t • (R (J z) - m • z)) ≫ i ≫ i') ≫ r' := by simp only [Category.assoc]
        _ = 1 := by rw [h2, MonObj.one_comp]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hy0 : R (J z) - m • z = 0 := LatticeHom.eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => by
      rw [← u.ker]
      have e := hkill _ (hker ((n : ℂ)⁻¹ * t))
      rw [← holUnif_ex_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← _root_.mul_assoc,
        mul_inv_cancel₀ hn0, _root_.one_mul] at e
      exact e
    exact sub_eq_zero.1 hy0

  obtain ⟨β, hβ, hβe⟩ := _root_.GlobalTheory.exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q Q Q.g v v (J ∘ₗ M ∘ₗ R)
    rfl rfl (fun l hl => hJΛ _ (hM _ (hRΛ _ hl)))
  haveI := hβ
  have hφ : ∀ z, u.ex z ≫ (i ≫ i') ≫ β ≫ (r' ≫ r) = u.ex ((m * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR, hRJ, hRJ, map_nsmul, smul_smul]
  have := hA.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A hA (m * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    ((i ≫ i') ≫ β ≫ (r' ≫ r)) fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m * m ≠ 0 by positivity)
  have hw : (m * m) • (((m * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u.ex (M w) = u.ex ((m * m) • M (((m * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m * m : ℕ) : ℂ)⁻¹ • w) ≫ (i ≫ i') ≫ β ≫ (r' ≫ r) := (hφ _).symm
    _ = u.ex (((m * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

end GlobalTheory.HolUnifEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRightInvOfSpan
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem exists_rightInv_of_span {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  refine GlobalTheory.ZeroCycleHt.exists_rightInv fun v => ?_
  have hv : v ∈ Submodule.span F (Set.range w.col) := hw ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
  refine ⟨c, ?_⟩
  rw [← hc]
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem htMul : HtMul := by
  intro F _ _ B N n w A Λ hL
  obtain ⟨P, hP⟩ := exists_rightInv_of_span hL.spans
  refine ⟨fun a a' G G' hG hG' ha ha' => ?_, fun c hc => ?_⟩
  · exact GlobalTheory.ZeroCycleHt.formHeight_mul 0 0 hP hL.det hG hG' ha ha'
  · have h1 : IsMultiHomogeneous (fun _ : Fin B => 0) (1 : MvPolynomial (Fin B × Fin N) F) := by
      intro t ht b
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at ht
      split_ifs at ht with h
      · subst h; simp
      · exact absurd rfl ht
    have := GlobalTheory.HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det one_ne_zero h1 hc
    rw [mul_one, GlobalTheory.ZeroCycleHt.formHeight_one] at this
    exact this

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibre

variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)

theorem unitAt_square (x₁ x₂ : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_gen).1 S P (Over.mk t) x₁ x₂
    (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by
    rw [spec_pt_eq (k := K) q (IsLocalRing.closedPoint K)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (Over.mk t ⊗ P.A).left)
    ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem isIntegral_fibre : IsIntegral (Over.mk t ⊗ P.A).left := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  exact GeometricallyIntegral.geometrically_isIntegral (f := P.A.hom) t (pullback.snd t P.A.hom)
    (pullback.fst t P.A.hom) (IsPullback.of_hasPullback t P.A.hom).flip

def trY (w : Over.mk t ⟶ P.A) : Over.mk t ⊗ P.A ⟶ Over.mk t ⊗ P.A := lift (fst _ _) (translPt P.A w)

theorem trY_snd (w : Over.mk t ⟶ P.A) :
    (trY P t w).left ≫ (snd (Over.mk t) P.A).left = (translPt P.A w).left := by
  rw [← Over.comp_left, trY, lift_snd]

theorem lift_trY (a w : Over.mk t ⟶ P.A) : lift (𝟙 (Over.mk t)) a ≫ trY P t w = lift (𝟙 (Over.mk t)) (w * a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trY]
  · rw [Category.assoc, trY, lift_snd, lift_snd, translPt, comp_lift_assoc, lift_fst_assoc, Category.id_comp,
      lift_snd, Hom.mul_def]

theorem isUnit_sval_of_mem {X Y Z : Scheme.{0}} {L : LB X} {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {ε : I → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (h : r z ∈ nonzeroLocus s) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : IsUnit (sval s r z J) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval s r z hJ k hk

theorem exists_sec_twist_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (a : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ s : LB.Sec (twistLB P.A P.L 2 c), (lift (𝟙 (Over.mk t)) a).left p ∈ nonzeroLocus s := by
  intro S P K _ _ t c a p
  have hI := isIntegral_fibre P t
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_polarisation_section_nonempty_nonvanishing S P K t hI
  obtain ⟨u, h₁, h₂⟩ := _root_.GlobalTheory.AlgClosedFibre.exists_point_mem_translates S P K t inferInstance (nonzeroLocus θ) hθ a c p
  obtain ⟨g, hg⟩ := unitAt_square P t (c * u) u⁻¹ ((lift (𝟙 (Over.mk t)) a).left p)
  have hF : FormEq (Sum.elim (Sum.elim (fun k => (trY P t (c * u)).left ≫ ![(snd (Over.mk t) P.A).left] k)
      (fun k => (trY P t u⁻¹).left ≫ ![(snd (Over.mk t) P.A).left] k))
      ![(translPt P.A (c * u * u⁻¹)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A (c * u)).left, (translPt P.A u⁻¹).left])
      (Sum.elim (Sum.elim ![1] ![1]) ![1, 1, -1, -1])
      ![(snd (Over.mk t) P.A).left, (translPt P.A c).left] ![((2 : ℕ) : ℤ) - 1, 1] := by
    refine formEq_of_add fun U _ h => ?_
    simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]
    rw [trY_snd, trY_snd, mul_inv_cancel_right]
    simp
    abel
  obtain ⟨σ, hσ⟩ := exists_sec P.isLB hF (mulSec (mulSec (pullSec θ (trY P t (c * u)).left)
    (pullSec θ (trY P t u⁻¹).left)) g)
  refine ⟨σ, ?_⟩
  choose J hJ using fun χ : (Over.mk t ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ ((lift (𝟙 (Over.mk t)) a).left p))
  have hJ' : Good P.L ((lift (𝟙 (Over.mk t)) a).left p) J := hJ
  refine (GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval σ _ hJ').2 ?_
  rw [hσ _ _ _ J hJ', sval_mulSec _ _ _ _ hJ',
    sval_mulSec _ _ _ _ hJ', sval_pullSec _ _ _ _ hJ', sval_pullSec _ _ _ _ hJ']
  refine ((isUnit_sval_of_mem θ _ _ ?_ hJ').mul (isUnit_sval_of_mem θ _ _ ?_ hJ')).mul (hg J hJ')
  · rw [Category.id_comp, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_trY]
    exact h₁
  · rw [Category.id_comp, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_trY]
    exact h₂

end GlobalTheory.TwistFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAtInfinityAdeleWithComplexCompone
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RealLift

theorem exists_atInf_piInf_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (f : InfinitePlace F → ℂ),
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) z ∧ ∀ w, piInf (emb w) z = f w := by
  intro F E _ _ _ _ _ σ h emb f
  have := h.1

  have him : ∀ (τ : E →+* ℂ) (e : E), σ e ≠ e → (τ e).im ≠ 0 := fun τ e he him => by
    apply he
    apply τ.injective
    rw [h.2.2.2 τ e]
    exact Complex.conj_eq_iff_im.2 him
  by_cases hσ : ∃ e : E, σ e ≠ e
  swap
  · push_neg at hσ
    refine ⟨0, fun u _ => smul_zero u, fun w => ?_⟩
    exfalso
    have := h.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (emb w).1)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact (h.2.2.2 (emb w).1 x).symm.trans (congrArg _ (hσ x))
  obtain ⟨e, he⟩ := hσ
  let lift : ∀ w : InfinitePlace F, ℝ → w.Completion := fun w t =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm t
  have hlift : ∀ w t, InfinitePlace.Completion.extensionEmbedding w (lift w t) = (t : ℂ) := fun w t => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
    exact congrArg _ ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply t)
  let c : InfinitePlace F → ℝ := fun w => (f w).im / ((emb w).1 e).im
  let a : InfinitePlace F → ℝ := fun w => (f w).re - c w * ((emb w).1 e).re
  let A : AF F := ((fun w => lift w (a w) : Ainf F), 0)
  let C : AF F := ((fun w => lift w (c w) : Ainf F), 0)
  refine ⟨A ⊗ₜ[F] (1 : E) + C ⊗ₜ[F] e, fun u hu => ?_, fun w => ?_⟩
  · have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    have hA : u * A = 0 := by
      show ((u.1 * A.1, u.2 * (0 : Af F)) : Ainf F × Af F) = ((0, 0) : Ainf F × Af F)
      rw [hu1, zero_mul, mul_zero]
    have hC : u * C = 0 := by
      show ((u.1 * C.1, u.2 * (0 : Af F)) : Ainf F × Af F) = ((0, 0) : Ainf F × Af F)
      rw [hu1, zero_mul, mul_zero]
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hA, hC,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · change infEmb (emb w) (compInf F E w (A ⊗ₜ[F] (1 : E) + C ⊗ₜ[F] e)) = f w
    rw [map_add (f := _)]
    change infEmb (emb w) (evInf F w A ⊗ₜ[F] (1 : E) + evInf F w C ⊗ₜ[F] e) = f w
    rw [map_add (f := _), infEmb_tmul, infEmb_tmul, map_one, mul_one]
    change InfinitePlace.Completion.extensionEmbedding w (lift w (a w)) +
      InfinitePlace.Completion.extensionEmbedding w (lift w (c w)) * (emb w).1 e = f w
    rw [hlift, hlift]
    have hne := him (emb w).1 e he
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, a]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, zero_add, c]
      field_simp

end GlobalTheory.RealLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHomFrameConjugationAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_hom_frame_conjugation_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] (σL : L →+* L) (δ : L)
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), δ ≠ 0 → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      ∀ (P JT : GL (Fin n) L), (JT : Matrix (Fin n) (Fin n) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι P X.J)ᵀ →
      ∃ iW : Formalism.UG.UJ σL (JT : Matrix (Fin n) (Fin n) L) →* UA σ X.J, ∀ h,
        mat (iW h) = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι := by
  first | exact @GlobalTheory.InertLocFrame.HomW.homW | exact GlobalTheory.InertLocFrame.HomW.homW | (intros; apply GlobalTheory.InertLocFrame.HomW.homW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinDiv
section
noncomputable section

namespace GlobalTheory.FinSupp

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable (F : Type) [Field F] [NumberField F]

def FinDiv (N : ℕ) (a : AF F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ b ∈ v.adicCompletionIntegers F, evFin F v a = (N : Fv F v) * b

def finPart (a : AF F) : AF F := (0, a.2)

end GlobalTheory.FinSupp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumPiTensorHeisenbergFactorwiseSignatureStatement
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vacuum_pi_tensor_heisenberg_factorwise_signature : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ} (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
    sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  first | exact @GlobalTheory.FockVacD.sumPl_heisOp_vacuum_dep | exact GlobalTheory.FockVacD.sumPl_heisOp_vacuum_dep | (intros; apply GlobalTheory.FockVacD.sumPl_heisOp_vacuum_dep <;> assumption)
end

