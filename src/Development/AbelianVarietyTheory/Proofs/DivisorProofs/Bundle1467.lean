module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapDegEqPowMulCard
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.ZV GlobalTheory.DegKer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbelianTower

theorem finrank_eq_of_mapDeg {X Y : Scheme.{0}} [IsIntegral Y] (φ : X ⟶ Y) [IsFinite φ] [Flat φ] {D : ℕ}
    (hD : MapDeg φ D) (y : Y) : φ.finrank y = D := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  letI := (φ.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := φ.finite_app U hU
  haveI : Module.Flat Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
    have := φ.flat_appLE hU (hU.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hp : IsPullback (hU.preimage φ).fromSpec (Spec.map (φ.app U)) φ hU.fromSpec :=
    (IsOpenImmersion.isPullback _ _ _ _ (by
      rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hU (hU.preimage φ)])
      (by simp)).flip
  obtain ⟨q, rfl⟩ : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hy
  rw [← hD.finrank_eq U hU ⟨_, hy⟩, ← FiniteCover.rankAtStalk_bot,
    Module.rankAtStalk_eq_of_le_of_finite_of_flat _ (p := ⊥) (q := q) bot_le,
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp q]
  exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) _

end GlobalTheory.SemiAbelianTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReading
section
set_option autoImplicit false

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.GeoLevel

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}


set_option maxHeartbeats 800000 in
theorem exists_isometry_of_move_deriv {g : ℕ} {σ' : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) {i : Fin F.n} {P P' : (F.Di i).La →+ (Fin g → ℂ)}
    (p : IsPeriod (F.Di i) ty P) (p' : IsPeriod (F.Di i) ty P') (hu : F.u i P ≫ ρ = F.u i P')
    (hd : ∀ j, ∃ v, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single j 1) v ∧
      IsDerivAt0 (fun z => (F.ex i P' z).left) (Pi.single j 1) (v ≫ ν.φ)) :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) ∧
      (∀ a, P' (gam a) = P a) ∧ ∀ z, (F.ex i P' z).left = (F.ex i P z).left ≫ ν.φ := by
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p' hu
  have hcol : ∀ j, h.toLinearMap (Pi.single j 1) = Pi.single j 1 := by
    intro j
    obtain ⟨v, hv, d1⟩ := hd j
    have d0 := FibreDeriv.isDerivAt0_comp hv ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have hid : h.toLinearMap = LinearMap.id := by
    refine (Pi.basisFun ℂ (Fin g)).ext fun j => ?_
    rw [Pi.basisFun_apply, hcol, LinearMap.id_apply]
  have hz : ∀ z, h z = z := fun z => LinearMap.congr_fun hid z
  exact ⟨gam, hiso, fun a => by rw [hh, hz], fun z => by rw [← hex, hz]⟩


set_option maxHeartbeats 1600000 in
theorem evR_normUn_move {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
    {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k) {un : (M.X k).dom → FrPt Xo c (CAt σ)}
    (hun : IsNormUn T un) (x x' : (M.X k).dom) (A : Matrix (Fin r) (Fin r) E)
    (hA : A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E))
    (hper : ∀ a, ∃ a', (M.φ k a' : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) ∧ T.Pf x'.1 a' = T.Pf x.1 a)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) (hρ : ρ ≫ Xo.s = Xo.s)
    (hx : (un x').x = (un x).x ≫ ρ) (hu : ∀ τ i, (un x').u τ i = (un x).u τ i ≫ ν.φ)
    {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hw : Dom w n) {f f' : Rul Xo c} (hf : f ∈ sec Xo c w n)
    (hff : ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') :
    evR Xo c f' (un x) = evR Xo c f (un x') := by
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun x'
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm x'.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x'.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x'.2
  have p := T.isPer _ hb
  have p' := T.isPer _ hb'
  obtain ⟨gam, hiso, hP, hex⟩ := exists_isometry_of_move_deriv F ν p p'
    ((congrArg (· ≫ ρ) hy.1).symm.trans (hx.symm.trans hy'.1)) (fun j => by
      obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
      exact ⟨_, hy.2.1 τ i, hu τ i ▸ hy'.2.1 τ i⟩)
  have hgam : ∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) := fun a => by
    obtain ⟨a', h1, h2⟩ := hper a
    have h3 : gam a = a' := p'.2.1 (by rw [hP, T.co.apply_symm_apply, T.co.apply_symm_apply, h2])
    rw [h3, h1]
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (un x)).1
  obtain ⟨t₀, ht⟩ := exists_frBor_gen (un x') y' (hmv.1.trans hx.symm)
    (funext fun τ => funext fun i => (hmv.2.1 τ i).trans (hu τ i).symm)
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have d1 := (T.norm _ hb).1.ne_zero
  have d2 := (T.norm _ hb').1.ne_zero
  have k1 : κ ≠ 0 := fun h0 => mul_ne_zero hC d1 (by rw [← hκ, h0]; simp)
  have k2 : κ' ≠ 0 := fun h0 => mul_ne_zero hC d2 (by rw [← hκ', h0]; simp)
  have hth := _root_.GlobalTheory.GeoLevel.theta_move_sq E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un x) (un x') y' gam A ρ ν _ k1 k2 hy hy'
    hiso hgam hA hP hex hmv ht
  have ht2 : Formalism.L2.PjFree.toC (t₀ : CAt σ) ^ 2 = 1 := by
    rw [hκ, hκ'] at hth
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d2) d1) ?_
    refine hth.trans ?_
    ring
  have hred : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  rw [hff _ _ hmv, (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred w n f hf _ _ _ ht,
    wchar_ex_sign Dw _ ht2 (fun _ => rfl) w n hw.2, one_mul]

theorem exists_isMatch_of_models (D : Datum H) {X X' : Data E r} (φ : D.La ≃ₗ[𝓞 E] X.Λ) (φ' : D.La ≃ₗ[𝓞 E] X'.Λ)
    (hΨ : X.Ψ = X'.Ψ) (hp : X.p0 = X'.p0) (hG : X'.Gm = X.Gm) (hξ : X'.ξ0 = X.ξ0)
    (ef : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (ef' : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → E) (φ' b))) :
    ∃ δ : GL (Fin r) E, IsMatch X X' δ ∧
      ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := by
  have hs : ∀ (Y : Data E r) (ψ : D.La ≃ₗ[𝓞 E] Y.Λ), Function.Injective (Y.Λ.subtype ∘ₗ ψ.toLinearMap) ∧
      Submodule.span E (Set.range (Y.Λ.subtype ∘ₗ ψ.toLinearMap)) = ⊤ := fun Y ψ => by
    refine ⟨Subtype.val_injective.comp ψ.injective, ?_⟩
    rw [← Y.Λ_span]
    congr 1
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (ψ a).2
    · intro hv
      exact ⟨ψ.symm ⟨v, hv⟩, congrArg Subtype.val (ψ.apply_symm_apply _)⟩
  have hc : cc (-X.ξ0) = -(-X.ξ0) := by
    have := X.ξ0_im
    unfold cc at this ⊢
    rw [map_neg, this]
  rw [hG, hξ] at ef'
  obtain ⟨δ, h1, h2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H D D r (-X.ξ0) X.Gm
    (X.Λ.subtype ∘ₗ φ.toLinearMap) (X'.Λ.subtype ∘ₗ φ'.toLinearMap) (LinearEquiv.refl _ _) hc
    ⟨(hs X φ).1, (hs X φ).2, X.Gm_herm, X.Gm_det, ef⟩ ⟨(hs X' φ').1, (hs X' φ').2, X.Gm_herm, X.Gm_det, ef'⟩
    (fun _ _ => rfl)
  have h3 : ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := h2
  refine ⟨δ, ⟨hΨ, hp, hξ.symm, fun u v => by rw [hG, h1], fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩, h3⟩
  · have := h3 (φ.symm ⟨v, hv⟩)
    rw [φ.apply_symm_apply] at this
    exact this ▸ (φ' _).2
  · have := h3 (φ'.symm ⟨_, hv⟩)
    rw [φ'.apply_symm_apply] at this
    have e := congrArg (fun u => ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) this
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e
    rw [e]
    exact (φ _).2

end


set_option maxHeartbeats 3200000 in
theorem rdU_move_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (φD : Dw.La →ₗ[𝓞 E] (Fin r → E)), Function.Injective φD → Submodule.span E (Set.range φD) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φD x) (φD y))) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ (U.X k).ξ0).im < 0) → ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ), ((δ : Matrix (Fin r) (Fin r) E).det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) E).det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k φD hinj hsp hEF hneg δ h hdet ρ ν hρ hmm w n hw f hf f' hf' hff x hx
  obtain ⟨g, e, F, ik, φ, ⟨hef, hpin⟩, hnorm⟩ := exists_pinned_of_isUnf hU
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F r
    (U.X k).ξ0 (U.X k).Gm φD (U.X k).ξ0_im hneg ⟨hinj, hsp, (U.X k).Gm_herm, (U.X k).Gm_det, hEF⟩
  have T : ∀ k, ThetaData e F M k := fun k => (_root_.GlobalTheory.FrameUnif.nonempty_thetaData E H Dw l Xo c σ g e F r M hσ hM hξ k).some
  choose un hun using fun k => _root_.GlobalTheory.FrameUnif.exists_isNormUn hT E H Dw l Xo c σ g e F r M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => _root_.GlobalTheory.NormFrame.frameOK_of_isNormUn hT E H Dw l Xo c σ g e F r M k (T k) (un k) hσ hM hξ (hun k),
      fun k => _root_.GlobalTheory.NormUnBor.normUn_bor hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun k => _root_.GlobalTheory.FrameUnif.normUn_gamma hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => _root_.GlobalTheory.FrameUnif.NormUnHol.differentiableOn_rdU hB hT E H Dw l Xo c σ g e F r M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F r M un hσ hM hξ hok
  obtain ⟨δ₀, h₀, hφ⟩ := exists_isMatch_of_models (F.Di (ik k)) (φ k) (M.φ (ik k))
    (Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hM.type (ik k)).2 τ).symm)
    ((hU.2.1 k).1.trans (hM.type (ik k)).1.symm) (hMG _).1 (hMG _).2 (hef k) (hM.ef _)
  have hPf : ∀ (y : Frame (U.X k).Ψ r) a j, (T (ik k)).Pf (lact δ₀ (castFr h₀.psi y)) a j =
      Formalism.L2.PjFree.perFr (U.X k) y (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2 := fun y a j => by
    rw [(T (ik k)).per, hφ]
    exact _root_.GlobalTheory.GeoLevel.perFr_lact_of_isMatch E r _ _ δ₀ h₀ y _ _ _
  have key : ∀ y : (U.X k).dom, (un (ik k) ⟨_, h₀.mem_dom y.2⟩).x = (U.un k y).x ∧
      (un (ik k) ⟨_, h₀.mem_dom y.2⟩).u = (U.un k y).u ∧
      (IsUnitFr (U.X k) y.1 → ∃ P : (F.Di (ik k)).La →+ (Fin g → ℂ),
        IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P ∧ (U.un k y).x = F.u (ik k) P ∧
        NormPin F (ik k) P (U.un k y) ∧ NormPin F (ik k) P (un (ik k) ⟨_, h₀.mem_dom y.2⟩)) := fun y => by
    obtain ⟨P, a1, a2, a3, a4⟩ := hpin k y
    obtain ⟨P', b1, -, b3, b4, b5⟩ := hok.1 (ik k) ⟨_, h₀.mem_dom y.2⟩
    obtain rfl : P' = P := AddMonoidHom.ext fun v => funext fun j =>
      (b1 v j).trans (((T (ik k)).per _ v j).symm.trans ((hPf y.1 v j).trans (a1 v j).symm))
    refine ⟨b3.trans a3.symm, funext fun τ => funext fun i =>
      ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ _ a2).2.1 _).unique (b4 τ i) (a4 τ i), fun hy =>
      ⟨P', a2, a3, hnorm k y P' a1 hy, b5 fun τ i => (congrArg norm (h₀.dmin_eq y.1 τ i)).trans (hy _ i)⟩⟩
  obtain ⟨ν₁, hν₁, hid⟩ := (GlobalTheory.MoveCalc.frMove_calculus E H Dw l Xo c).1
  have hmm₀ : MoveMatch U (unfOf e F M un) k (ik k) h₀ (𝟙 _) ν₁ := fun y y' hy =>
    ⟨hy.1.trans ((Category.comp_id _).trans (key y).1.symm), (funext fun τ => funext fun i =>
      (hy.2.1 τ i).trans ((congrArg _ hν₁).trans (Category.comp_id _))).trans (key y).2.1.symm⟩
  obtain ⟨ε, -, hε⟩ := _root_.GlobalTheory.GeoLevel.exists_const_rdU_of_moveMatch E H Dw l Xo c σ r U (unfOf e F M un) hσ hU hU₀ k (ik k) δ₀ h₀ (𝟙 _) ν₁
    (Category.id_comp _) hmm₀ (fun y y' t hy hmv hb => by
      obtain ⟨P, p, a1, a2, a3⟩ := (key y).2.2 hy
      exact cabs_gen_eq_one_of_normPin E H Dw l Xo c σ _ g _ F _ _ P P _ ν₁ _ _ y' t p p a1
        ((key y).1.trans a1) a2 a3 hmv hb) n
  have hself : ∀ (f₀ : Rul Xo c) (y y' : FrPt Xo c (CAt σ)), FrMove (𝟙 _) ν₁ y y' →
      evR Xo c f₀ y = evR Xo c f₀ y' := fun f₀ y y' hy => by
    rw [(GlobalTheory.exists_unique_frMove E H Dw l Xo c _ ν₁ (Category.id_comp _) (CAt σ) y).2 y y' ν₁ rfl (hid _ y) hy]
  have hx' := h.mem_dom hx
  rw [hε w hw f' hf' f' hf' (hself f') x hx, hε w hw f hf f hf (hself f) _ hx']
  refine congrArg (ε * ·) ?_
  refine (rdU_of_mem (unfOf e F M un) f' (ik k) (h₀.mem_dom hx)).trans
    (Eq.trans (congrArg Formalism.L2.PjFree.toC ?_) (rdU_of_mem (unfOf e F M un) f (ik k) (h₀.mem_dom hx')).symm)
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (U.un k ⟨x, hx⟩)).1
  obtain ⟨m1, m2⟩ := hmm ⟨x, hx⟩ y' hmv
  obtain ⟨k1, k2, -⟩ := key ⟨x, hx⟩
  obtain ⟨k3, k4, -⟩ := key ⟨_, hx'⟩
  refine evR_normUn_move (T (ik k)) (hun (ik k)) ⟨_, h₀.mem_dom hx⟩ ⟨_, h₀.mem_dom hx'⟩
    ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ?_ (fun a => ?_) ν hρ ?_ (fun τ i => ?_) hw hf hff
  · have : ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det = (δ : Matrix (Fin r) (Fin r) E).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    rw [this]
    exact hdet
  · obtain ⟨a', ha'⟩ := (φ k).surjective ⟨_, (h.lat _).1 (φ k a).2⟩
    have ha : (φ k a' : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) := congrArg Subtype.val ha'
    refine ⟨a', ?_, funext fun j => ?_⟩
    · rw [hφ, hφ, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, Units.inv_mul,
        Matrix.mul_one, Units.val_mul]
    · refine (hPf _ a' j).trans (Eq.trans ?_ (hPf _ a j).symm)
      rw [ha]
      exact _root_.GlobalTheory.GeoLevel.perFr_lact_of_isMatch E r _ _ δ h x _ _ _
  · exact k3.trans (m1.symm.trans (hmv.1.trans (congrArg (· ≫ ρ) k1.symm)))
  · exact (congrFun (congrFun (k4.trans m2.symm) τ) i).trans
      ((hmv.2.1 τ i).trans (congrArg (· ≫ ν.φ) (congrFun (congrFun k2.symm τ) i)))

end GlobalTheory.GeoLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdOfDvdIterates
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

noncomputable section

namespace GlobalTheory.MuDivides

private theorem mem_span_pow_smul_univ_iff_dvd {R : Type} [CommRing R] (q x : R) (n : ℕ) :
    x ∈ (Ideal.span {q} ^ n • ⊤ : Submodule R R) ↔ q ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem dvd_of_step {R : Type} [CommRing R] (q a : R) [IsAdicComplete (Ideal.span {q}) R]
    (P : R → Prop) (h : ∀ z, P z → ∃ y z₁, z = a * y + q * z₁ ∧ P z₁) (z : R) (hz : P z) :
    a ∣ z := by
  choose Y Z hYZ using h

  let s : ℕ → {w : R // P w} := fun n =>
    Nat.rec ⟨z, hz⟩ (fun _ w => ⟨Z w.1 w.2, (hYZ w.1 w.2).2⟩) n
  obtain ⟨w, y, hw0, hw⟩ : ∃ w y : ℕ → R, w 0 = z ∧ ∀ n, w n = a * y n + q * w (n + 1) :=
    ⟨fun n => (s n).1, fun n => Y (s n).1 (s n).2, rfl, fun n => (hYZ _ _).1⟩

  have key : ∀ n, z = a * (∑ k ∈ Finset.range n, q ^ k * y k) + q ^ n * w n := by
    intro n
    induction n with
    | zero => simp [hw0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hw n]
      ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {q}) (M := R) inferInstance
    (f := fun n => ∑ k ∈ Finset.range n, q ^ k * y k) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_span_pow_smul_univ_iff_dvd]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨-∑ j ∈ Finset.range d, q ^ j * y (m + j), ?_⟩
      rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
      simp only [pow_add, mul_assoc, sub_add_cancel_left])
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {q}) (M := R) inferInstance _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_span_pow_smul_univ_iff_dvd]
  have hn := hL n
  rw [SModEq.sub_mem, mem_span_pow_smul_univ_iff_dvd] at hn
  obtain ⟨c, hc⟩ := hn
  exact ⟨a * c + w n, by linear_combination key n + a * hc⟩

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]


omit [IsAlgClosed C] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem modP_isNilpotent_of_not_isUnit (hv : v.Integers O) (x : ModP O p) (hx : ¬IsUnit x) : IsNilpotent x := by
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O)}) x

  have hlt : v (algebraMap O C o) < 1 := by
    refine lt_of_le_of_ne (hv.map_le_one o) fun h1 => hx ?_
    exact (hv.isUnit_of_one' h1).map _

  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast]
    exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hp0 hlt
  refine ⟨n, ?_⟩
  have hdvd : (p : O) ∣ o ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hdvd)


omit [IsAlgClosed C] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem eq_zero_of_forall_pow_dvd (hv : v.Integers O) (c m : PreTilt O p) (hc : ¬IsUnit c)
    (h : ∀ n, c ^ p ^ n ∣ m) : m = 0 := by
  have h0 : ¬IsUnit (PreTilt.coeff 0 c) := fun hu => hc (GlobalTheory.AinfXi.isUnit_of_coeff_zero hu)
  obtain ⟨N, hN⟩ := modP_isNilpotent_of_not_isUnit hv _ h0
  refine Perfection.ext (R := ModP O p) (p := p) fun k => ?_
  rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, map_zero]
  obtain ⟨d, hd⟩ := h (k + N)

  rw [hd, map_mul, map_pow, pow_add, pow_mul, GlobalTheory.AinfXi.coeff_pow_pow_zero,
    pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le hN, zero_mul]

omit [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem root_iterate_pow (n : ℕ) (ε : PreTilt O p) : (root^[n] ε) ^ p ^ n = ε :=
  iterate_frobeniusEquiv_symm_pow_p_pow (PreTilt O p) p ε n

theorem tilt_dvd (hv : v.Integers O) (ε : PreTilt O p) (hm : ε - 1 ≠ 0) (w : PreTilt O p)
    (h : ∀ n : ℕ, ε - 1 ∣ (root^[n] ε - 1) * w) : ε - 1 ∣ w := by
  obtain ⟨hD, hV⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv

  have ht : ∀ n : ℕ, (root^[n] ε - 1) ^ p ^ n = ε - 1 := fun n => by
    rw [sub_pow_char_pow, one_pow, root_iterate_pow]
  rcases ValuationRing.dvd_total (ε - 1) w with hw | ⟨u, hu⟩
  · exact hw
  by_cases hu' : IsUnit u
  · exact hu'.dvd_mul_right.1 (by rw [← hu])

  exfalso
  refine hm (eq_zero_of_forall_pow_dvd hv u (ε - 1) hu' fun n => ?_)
  have h1 : (ε - 1) * u ∣ (ε - 1) * (root^[n] ε - 1) := by
    have := mul_dvd_mul_right (h n) u
    rwa [mul_assoc, ← hu, mul_comm (root^[n] ε - 1)] at this
  have hut : u ∣ root^[n] ε - 1 := (mul_dvd_mul_iff_left hm).1 h1
  simpa only [ht n] using pow_dvd_pow_of_dvd hut (p ^ n)

omit [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem constantCoeff_mu (ε : PreTilt O p) : WittVector.constantCoeff (mu ε) = ε - 1 := by
  rw [mu, map_sub, map_one,
    show WittVector.constantCoeff (WittVector.teichmuller p ε) = ε from
      WittVector.teichmuller_coeff_zero p ε]

omit [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem exists_eq_p_mul (x : Ainf p O) (hx : WittVector.constantCoeff x = 0) :
    ∃ y, x = (p : Ainf p O) * y :=
  Ideal.mem_span_singleton.1 ((WittVector.mem_span_p_iff_coeff_zero_eq_zero x).2 hx)

theorem dvd_of_dvd_p_mul (hv : v.Integers O) (ε : PreTilt O p) (hm : ε - 1 ≠ 0) (w : Ainf p O)
    (h : mu ε ∣ (p : Ainf p O) * w) : mu ε ∣ w := by
  obtain ⟨hD, -⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv
  obtain ⟨c, hc⟩ := h

  have hc0 : WittVector.constantCoeff c = 0 := by
    have h0 := congrArg WittVector.constantCoeff hc
    rw [map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, constantCoeff_mu] at h0
    exact (mul_eq_zero.1 h0.symm).resolve_left hm
  obtain ⟨c', rfl⟩ := exists_eq_p_mul c hc0
  refine ⟨c', sub_eq_zero.1 (WittVector.eq_zero_of_p_mul_eq_zero _ ?_)⟩
  linear_combination hc

theorem mu_dvd_of_forall_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ z : Ainf p O, (∀ n : ℕ, mu ε ∣ mu (root^[n] ε) * z) → mu ε ∣ z := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε z hz
  have hm : ε - 1 ≠ 0 := by
    rw [← constantCoeff_mu]
    exact (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).1
  refine dvd_of_step (p : Ainf p O) (mu ε) (fun x => ∀ n : ℕ, mu ε ∣ mu (root^[n] ε) * x) ?_ z hz
  intro x hx

  obtain ⟨b, hb⟩ : ε - 1 ∣ WittVector.constantCoeff x := by
    refine tilt_dvd hv ε hm _ fun n => ?_
    have h1 := map_dvd WittVector.constantCoeff (hx n)
    rwa [map_mul, constantCoeff_mu, constantCoeff_mu] at h1

  obtain ⟨z₁, hz₁⟩ := exists_eq_p_mul (x - mu ε * WittVector.teichmuller p b) (by
    rw [map_sub, map_mul, constantCoeff_mu, hb, sub_eq_zero,
      show WittVector.constantCoeff (WittVector.teichmuller p b) = b from
        WittVector.teichmuller_coeff_zero p b])
  refine ⟨WittVector.teichmuller p b, z₁, by rw [← hz₁]; ring, fun n => ?_⟩

  apply dvd_of_dvd_p_mul hv ε hm
  have h1 : mu ε ∣ mu (root^[n] ε) * (x - mu ε * WittVector.teichmuller p b) := by
    rw [mul_sub]
    exact dvd_sub (hx n) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  rwa [hz₁, mul_left_comm] at h1

end GlobalTheory.MuDivides
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat


open GlobalTheory.HodgeTateCompare in
theorem omega_free_finite_bijective_of_smooth {O : Type} [CommRing O] [IsLocalRing O]
    (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [Smooth G.hom] :
    Module.Free O (omega G) ∧ Module.Finite O (omega G) ∧
      Function.Bijective (fun (x : LieG G) => ((LinearMap.proj x : (LieG G → O) →ₗ[O] O) ∘ₗ
        (omega G).subtype : Module.Dual O (omega G))) := by
  obtain ⟨h₁, h₂⟩ := finite_projective_of_smooth (G := G)
  haveI : Module.Free O (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) := Module.free_of_flat_of_isLocalRing
  refine ⟨.of_equiv (omegaEquiv G), .equiv (omegaEquiv G), ?_⟩
  refine (Function.Bijective.of_comp_iff _ (lieEquiv G).bijective).1 ?_
  refine (Function.Bijective.of_comp_iff' (omegaEquiv G).dualMap.bijective _).1 ?_
  convert Function.bijective_id
  funext w
  exact LinearMap.ext fun f => ev_apply f w

theorem Point.omega_free_finite_bijective : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), Module.Free O (omega P.Gt) ∧ Module.Finite O (omega P.Gt) ∧ Function.Bijective (fun (x : LieG P.Gt) => ((LinearMap.proj x : (LieG P.Gt → O) →ₗ[O] O) ∘ₗ (omega P.Gt).subtype : Module.Dual O (omega P.Gt))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  haveI := P.isLocalRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  exact omega_free_finite_bijective_of_smooth P.Gt

end GlobalTheory.HTLat
end

