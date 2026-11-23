module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0797
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLiftBaseChangeGlobalOneFormsAffinePreimag
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_bijective_of_isBaseChange {R R' B B' W W' Ω Ω' : Type} [CommRing R]
    [CommRing R'] [Algebra R R'] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R' B']
    [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R' W']
    [AddCommGroup Ω] [Module R Ω] [Module B Ω] [IsScalarTower R B Ω]
    [AddCommGroup Ω'] [Module R' Ω'] [Module B' Ω'] [IsScalarTower R' B' Ω']
    (α : B →+* B') (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h1 : Function.Surjective (liftSemi f))
    (m : Ω →ₛₗ[algebraMap R R'] Ω') (hm : ∀ (b : B) (ω : Ω), m (b • ω) = α b • m ω)
    (h2 : Function.Bijective (liftSemi m))
    (e : W →ₗ[R] Ω) (he : IsBaseChange B e) (e' : W' →ₗ[R'] Ω') (he' : IsBaseChange B' e')
    (p : W →ₛₗ[algebraMap R R'] W') (hp : ∀ w, e' (p w) = m (e w)) :
    Function.Bijective (LinearMap.lTensor B' (liftSemi p)) := by
  letI : Module R (B' ⊗[R'] (R' ⊗[R] W)) := Module.compHom _ (algebraMap R R')
  have hsm : ∀ (c : R) (z : B' ⊗[R'] (R' ⊗[R] W)), c • z = algebraMap R R' c • z := fun _ _ ↦ rfl
  have hR : ∀ (c : R) (x : R' ⊗[R] B), c • x = algebraMap R R' c • x := fun c x ↦
    (algebraMap_smul R' c x).symm
  have hW : ∀ (c : R) (w : W), (1 : R') ⊗ₜ[R] (c • w) = algebraMap R R' c • ((1 : R') ⊗ₜ[R] w) := by
    intro c w
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
      Algebra.algebraMap_eq_smul_one]

  let bil : R' ⊗[R] B →ₗ[R] W →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    LinearMap.mk₂ R (fun x w ↦ liftSemi f x ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] w))
      (fun x y w ↦ by rw [map_add (f := _), TensorProduct.add_tmul])
      (fun c x w ↦ by rw [hR, map_smul, hsm, TensorProduct.smul_tmul'])
      (fun x w w' ↦ by rw [TensorProduct.tmul_add, TensorProduct.tmul_add])
      (fun c x w ↦ by rw [hW, TensorProduct.tmul_smul, hsm])
  let Ψ : R' ⊗[R] (B ⊗[R] W) →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    TensorProduct.lift bil ∘ₗ (TensorProduct.assoc R R' B W).symm.toLinearMap
  have hΨ : Function.Surjective Ψ := by
    suffices hall : ∀ z, z ∈ LinearMap.range Ψ from
      LinearMap.range_eq_top.1 (eq_top_iff.2 fun z _ ↦ hall z)
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul b t =>
      induction t using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
      | tmul r w =>
        obtain ⟨x, hx⟩ := h1 (r • b)
        refine ⟨TensorProduct.assoc R R' B W (x ⊗ₜ w), ?_⟩
        have e1 : r ⊗ₜ[R] w = r • ((1 : R') ⊗ₜ[R] w) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          TensorProduct.lift.tmul, bil, LinearMap.mk₂_apply, hx, e1, ← TensorProduct.smul_tmul]
  let Θ : R' ⊗[R] (B ⊗[R] W) ≃ₗ[R] R' ⊗[R] Ω := (he.equiv.restrictScalars R).lTensor R'
  have hΘ : Function.Bijective (fun z ↦ liftSemi m (Θ z)) := h2.comp Θ.bijective
  have key : ∀ z, he'.equiv (LinearMap.lTensor B' (liftSemi p) (Ψ z)) = liftSemi m (Θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    | tmul r t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
      | tmul b w =>
        simp only [Ψ, Θ, bil, LinearMap.comp_apply, LinearEquiv.coe_coe,
          TensorProduct.assoc_symm_tmul, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
          liftSemi_tmul, LinearMap.lTensor_tmul, LinearEquiv.lTensor_tmul,
          LinearEquiv.restrictScalars_apply, IsBaseChange.equiv_tmul, one_smul, hf, hp, hm,
          map_smul, smul_assoc]
  refine ⟨fun x y hxy ↦ ?_, fun q ↦ ?_⟩
  · obtain ⟨x0, rfl⟩ := hΨ x
    obtain ⟨y0, rfl⟩ := hΨ y
    have := hΘ.1 (show liftSemi m (Θ x0) = liftSemi m (Θ y0) by rw [← key, ← key, hxy])
    rw [this]
  · obtain ⟨z, hz⟩ := hΘ.2 (he'.equiv q)
    refine ⟨Ψ z, he'.equiv.injective ?_⟩
    rw [key]; exact hz

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_pullForm_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → ∀ U : X.affineOpens, IsAffineOpen (φ ⁻¹ᵁ U.1) → Function.Bijective (LinearMap.lTensor (Sec s' (φ ⁻¹ᵁ U.1)) (liftSemi (pullForm h.w))) := by
  intro R R' _ _ _ X X' s s' φ h hF hH hF' hH' U hU
  let U' : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, hU⟩
  let pr : Pair φ := ⟨(U', U), le_rfl⟩
  have hsemi : SemiHom (algebraMap R R') (GlobalTheory.CechDR.secPull s s' pr) := GlobalTheory.CechDR.semiHom_secPull h.w pr
  let f : Sec s U.1 →ₛₗ[algebraMap R R'] Sec s' (φ ⁻¹ᵁ U.1) :=
    { toFun := GlobalTheory.CechDR.secPull s s' pr, map_add' := map_add _, map_smul' := hsemi }
  have h1 : Function.Bijective (liftSemi f) :=
    GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h pr rfl f (fun _ ↦ rfl)
  have h2 : Function.Bijective (liftSemi hsemi.m1) :=
    GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (GlobalTheory.CechDR.secPull s s' pr) hsemi f (fun _ ↦ rfl) h1
  let e : GlobForm s →ₗ[R] Ω[Sec s U.1⁄R] :=
    { toFun := fun w ↦ w.1 (Opposite.op U), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he : IsBaseChange (Sec s U.1) e :=
    isBaseChange_glob1 R (AffOp X) (OAff s) hF hH (Opposite.op U) e (fun _ ↦ rfl)
  let e' : GlobForm s' →ₗ[R'] Ω[Sec s' (φ ⁻¹ᵁ U.1)⁄R'] :=
    { toFun := fun w ↦ w.1 (Opposite.op U'), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he' : IsBaseChange (Sec s' (φ ⁻¹ᵁ U.1)) e' :=
    isBaseChange_glob1 R' (AffOp X') (OAff s') hF' hH' (Opposite.op U') e' (fun _ ↦ rfl)
  exact lTensor_liftSemi_bijective_of_isBaseChange (GlobalTheory.CechDR.secPull s s' pr) f (fun _ ↦ rfl) h1.2 hsemi.m1
    (fun b ω ↦ hsemi.oneFormMap_smul_semilinear b ω) h2 e he e' he' (pullForm h.w)
    (fun w ↦ ((isPullForm_iff.1 (isPullForm_pullForm h.w w)) pr).symm)

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaBoundFromMeasure
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem totallyComplex_core : IsTotallyComplex p.T.Q.c.F :=
  ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := p.T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

theorem goodOf_conj' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have e : (starRingEnd ℂ).comp σ = ComplexEmbedding.conjugate σ := by
    ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [e]; exact goodOf_conj (c := c) σ

theorem nrmK_conj (σ : p.T.Q.c.F →+* ℂ) (x : VK p.fw i) :
    nrmK p.fw i ((starRingEnd ℂ).comp σ) x = nrmK p.fw i σ x := by
  simp only [nrmK, normW, petW]
  rw [goodOf_conj']

theorem slopeMax_all_le (Cm : ℝ) (hG : GramAt p i) (hM : MeasAt p i Cm) :
    slopeMax_sq (nrmR p.R.toRealDat i) (latAll p.R.toRealDat i) ≤
      slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) + 2 * (Cm * unitE p) := by
  haveI := totallyComplex_core p
  obtain ⟨ι, h1, h2, h3⟩ := _root_.GlobalTheory.CovTop.SupImage.exists_emb_image_latW D _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  choose c hc0 hcB hcE using hM
  have hAll : latAll p.R.toRealDat i =
      Submodule.span (𝓞 D.what₂.LL) (ι '' (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) : Set (VK p.fw i))) := by
    unfold latAll; rw [h3]
  have hne : latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ≠ ⊥ := by
    intro h0
    apply hG.2.2.1
    refine le_bot_iff.1 ((latGood_le _ _ _).trans ((inf_le_left : latType p.R.toRealDat p.F.lv2 i ≤ latAll p.R.toRealDat i).trans ?_))
    change latAll p.R.toRealDat i ≤ ⊥
    rw [hAll, h0]
    simp
  have key := _root_.GlobalTheory.SlopeMaxExt.slopeMax_sq_span_le p.T.Q.c.F D.what₂.LL (VK p.fw i) (Fin (p.R.toRealDat.nW i) → D.what₂.LL) (nrmK p.fw i)
    (nrmR p.R.toRealDat i) ι (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) c (Cm * unitE p) hG.2.2.2.1 hG.1 (nrmK_conj p i) h2
    hG.2.2.2.2.1 hne (fun σ => ⟨hc0 σ, hcB σ⟩) (fun σ x => by
      obtain ⟨h, e⟩ := h1 x
      rw [e]
      exact hcE σ ⟨x, h⟩)
  rw [hAll]
  exact key

theorem unitE_le {PP A M : ℝ} (hH : HostNum D L PP A M) (hW : WtNum p i PP) :
    unitE p ≤ L.sc.x ^ (A + 1) * L.sc.b := by
  rw [hW.unit]
  have hX : 10 ≤ L.sc.x := hH.big.2.1.trans hH.big.2.2.1
  have hX0 : 0 < L.sc.x := by linarith
  have hL0 : 0 ≤ L.sc.L := by linarith [hH.big.2.1]
  have hb : 0 ≤ L.sc.b := le_trans (by positivity) hH.room
  have hlog : Real.log L.sc.x ≤ L.sc.x - 1 := Real.log_le_sub_one_of_pos hX0
  have hlogpos : 0 < Real.log L.sc.x := Real.log_pos (by linarith)
  have hll : Real.log (Real.log L.sc.x) ≤ L.sc.x := by
    have := Real.log_le_sub_one_of_pos hlogpos
    linarith
  have hll0 : 0 ≤ Real.log (Real.log L.sc.x) := by linarith [hH.big.2.2.2]
  have hmr : D.R.m ≤ D.R.r * D.R.nV := by
    have h1 : D.R.m ≤ D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
    have h2 : 1 ≤ D.R.nV := by have := D.R.two_le_m; unfold Ranks.nV; omega
    exact h1.trans (Nat.le_mul_of_pos_right _ h2)
  have hmr' : (D.R.m : ℝ) ≤ (D.R.r : ℝ) * D.R.nV := by exact_mod_cast hmr
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hfm : (D.R.f : ℝ) * D.R.m * L.sc.L ≤ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L := by
    have := mul_le_mul_of_nonneg_left hmr' hf
    have := mul_le_mul_of_nonneg_right this hL0
    linarith
  have hpoly := hH.poly.2.2
  have hfm0 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.L := by positivity
  calc (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x)
        = ((D.R.f : ℝ) * D.R.m * L.sc.L) * (L.sc.b * Real.log (Real.log L.sc.x)) := by ring
    _ ≤ L.sc.x ^ A * (L.sc.b * L.sc.x) :=
        mul_le_mul (hfm.trans hpoly) (mul_le_mul_of_nonneg_left hll hb) (by positivity) (by positivity)
    _ = L.sc.x ^ (A + 1) * L.sc.b := by rw [Real.rpow_add_one hX0.ne']; ring

theorem le_rpow_of_add {X b A1 A Cm u s : ℝ} (hX : 10 ≤ X) (hb : 0 ≤ b) (hA1 : 0 ≤ A1) (hA : 0 ≤ A) (hCm : 0 ≤ Cm)
    (hu : u ≤ X ^ (A + 1) * b) (hs : s ≤ X ^ A1 * b + 2 * (Cm * u)) :
    s ≤ X ^ (A1 + (A + 1) + (⌈2 * Cm⌉₊ : ℝ)) * b := by
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ X ^ A1 := Real.one_le_rpow (by linarith) hA1
  have hQ : 1 ≤ X ^ (A + 1) := Real.one_le_rpow (by linarith) (by linarith)
  have hK : 1 + 2 * Cm ≤ X ^ (⌈2 * Cm⌉₊ : ℝ) := by
    rw [Real.rpow_natCast]
    have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ X - 1 by linarith) ⌈2 * Cm⌉₊
    have h2 : 2 * Cm ≤ (⌈2 * Cm⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈2 * Cm⌉₊ : ℝ) ≤ (⌈2 * Cm⌉₊ : ℝ) * (X - 1) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
    have h4 : (1 : ℝ) + (X - 1) = X := by ring
    rw [h4] at h1
    linarith
  rw [Real.rpow_add hX0, Real.rpow_add hX0]
  set P := X ^ A1
  set Q := X ^ (A + 1)
  set K := X ^ (⌈2 * Cm⌉₊ : ℝ)
  have e1 : P * b ≤ P * Q * b := by
    have : P ≤ P * Q := le_mul_of_one_le_right (by linarith) hQ
    exact mul_le_mul_of_nonneg_right this hb
  have e2 : 2 * (Cm * u) ≤ 2 * Cm * (P * Q * b) := by
    have : u ≤ P * Q * b := hu.trans (by
      have : Q ≤ P * Q := le_mul_of_one_le_left (by linarith) hP
      exact mul_le_mul_of_nonneg_right this hb)
    nlinarith
  have e3 : P * Q * b * (1 + 2 * Cm) ≤ P * Q * b * K :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  nlinarith

end GlobalTheory.CovTop.LamAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolUnifHom


open GlobalTheory.SS GlobalTheory.EighthPowerFactor CechPic in
theorem exists_polAV_retract_dim (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g : ℕ)
    (hB : IsAbelianScheme B) (hd : SmoothOfRelativeDimension g B.hom) (M : LB B.left) (hM : M.IsLB)
    (ha : Out.RelAmple B M) (hK : Out.KTriv B M) :
    ∃ (Q : Out.PolAV (Sp k)) (i : B ⟶ Q.A) (r : Q.A ⟶ B),
      Q.g = 8 * g ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 B := by
  have := hB.comm
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  obtain ⟨W, hW, hbas⟩ := ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  let b : ZM.TBase k 1 := ⟨1, by simp, fun K _ β => by simp⟩
  have hc : (siegOne L₁.globalFns hB hM g).Principal :=
    ⟨relAmple_diag_lam hB hM (exists_gen_theta_of_isAbelianScheme k B hB M hM) ha,
      fun T x hx => SiegelOfPolarised.eq_one_of_lam hM hK x hx⟩
  obtain ⟨t, ⟨pr, hpr, hu, -⟩, -, -, -⟩ := exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g _ W _ a w w' bas hW hb
    hw hw' hs 1 k b _ (𝟙 _) (siegOne L₁.globalFns hB hM g) (one_pow _) odd_one hc hd
  obtain ⟨i, hi, -⟩ := hu B fun _ => 𝟙 B
  refine ⟨t.pol, i, pr 0, rfl, isMonHom_of_coord hpr hu fun u => ?_, hpr 0, hi 0⟩
  rw [hi u]
  exact inferInstanceAs (IsMonHom (𝟙 B))

end GlobalTheory.HolUnifHom

namespace GlobalTheory.HolUnifHom


open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel GlobalTheory.HolUnifEnd in
theorem exists_linear_factor (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hgA : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (u : HolUnif A L g) :
    ∃ (Q : Out.PolAV (Sp ℂ)) (v : HolUnif Q.A Q.L (8 * g)) (i : A ⟶ Q.A) (r : Q.A ⟶ A)
      (J : (Fin g → ℂ) →ₗ[ℂ] (Fin (8 * g) → ℂ)) (R : (Fin (8 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (m : ℕ),
      Q.g = 8 * g ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ (∀ z, v.ex (J z) = u.ex z ≫ i) ∧
      (∀ z, u.ex (R z) = v.ex z ≫ r) ∧ (∀ x ∈ u.Λ, J x ∈ v.Λ) ∧ (∀ x ∈ v.Λ, R x ∈ u.Λ) ∧
      ∀ z, R (J z) = m • z := by
  obtain ⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩ :=
    SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA
  obtain ⟨Q, i', r', hQg, hi', hr', hir'⟩ := exists_polAV_retract_dim ℂ B g hB hgB MB hMB hamp hK
  haveI := hi; haveI := hr; haveI := hi'; haveI := hr'
  suffices key : ∀ n, Q.g = n → ∃ (v : HolUnif Q.A Q.L n) (J : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ))
      (R : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, v.ex (J z) = u.ex z ≫ (i ≫ i')) ∧
      (∀ z, u.ex (R z) = v.ex z ≫ (r' ≫ r)) ∧ (∀ x ∈ u.Λ, J x ∈ v.Λ) ∧ (∀ x ∈ v.Λ, R x ∈ u.Λ) ∧
      ∀ z, R (J z) = m • z by
    obtain ⟨v, J, R, hJ, hR, hJΛ, hRΛ, hRJ⟩ := key (8 * g) hQg
    exact ⟨Q, v, i ≫ i', r' ≫ r, J, R, m, hQg, inferInstance, inferInstance, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩
  rintro n rfl
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -, -, -, -, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  have hu := TorusTransfer.tangent_bijective u hgA
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
  exact ⟨v, J, R, hJ, hR, hJΛ, hRΛ, hRJ⟩

end GlobalTheory.HolUnifHom

namespace GlobalTheory.HolUnifHom


open GlobalTheory.HolUnifEnd in
theorem exists_isMonHom_of_map_lattice :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g : ℕ), IsAbelianScheme A → IsAbelianScheme A' →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom →
    ∀ (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g) (u' : HolUnif A' L' g) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x ∈ u.Λ, M x ∈ u'.Λ) → ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  intro A A' _ _ g hA hA' hgA hgA' L L' u u' M hM
  obtain ⟨hL, -⟩ := abelianSchemeLaws_all
  obtain ⟨Q, v, i, r, J, R, m, hQ, hi, hr, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩ := exists_linear_factor A g hA hgA L u
  obtain ⟨Q', v', i', r', J', R', m', hQ', hi', hr', hm', hJ', hR', hJΛ', hRΛ', hRJ'⟩ :=
    exists_linear_factor A' g hA' hgA' L' u'
  obtain ⟨β, hβ, hβe⟩ := _root_.GlobalTheory.exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q Q' (8 * g) v v'
    (J' ∘ₗ M ∘ₗ R) hQ hQ' (fun l hl => hJΛ' _ (hM _ (hRΛ _ hl)))
  haveI := hi; haveI := hr'; haveI := hβ
  have hφ : ∀ z, u.ex z ≫ i ≫ β ≫ r' = u'.ex ((m' * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR', hRJ', hRJ, map_nsmul, smul_smul]
  have := hA'.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A' hA (m' * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    (i ≫ β ≫ r') fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u'.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m' * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' * m ≠ 0 by positivity)
  have hw : (m' * m) • (((m' * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u'.ex (M w) = u'.ex ((m' * m) • M (((m' * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ i ≫ β ≫ r' := (hφ _).symm
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m' * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

end GlobalTheory.HolUnifHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVacuumEqSmulIndicatorSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeVacuum_eq_smul_indicator_splitPlace : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ))
      (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)) (c : ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι ∧ ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  first | exact @GlobalTheory.VacShape.vacuum_eq_smul_indicator | exact GlobalTheory.VacShape.vacuum_eq_smul_indicator | (intros; apply GlobalTheory.VacShape.vacuum_eq_smul_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbedsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearlyDisjoint_of_flat_baseChange_embeds : ∀ (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L), (∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) → LinDisj (algebraMap R K) c θ := by
  first | exact @GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat | exact GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat | (intros; apply GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat <;> assumption)
end

