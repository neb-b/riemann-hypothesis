module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedOppositeLagrangianCoordinate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have h1 : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  have h2 : ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp
  intro h0
  apply h2
  rw [← h1, Matrix.det_mul, Matrix.det_mul, h0]
  simp

theorem exists_at_coBar_eq : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)),
    ∃ x : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x ∧ x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧ GlobalTheory.VacShape.coBar Bs Γ x = Y := by
  intro D a a' Bs Γ X om om' hTr Y
  have hcm := hTr.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have hV : Γ.V'.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_hasSig (hTr.geo.hV'.sig w)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hW : Γ.W.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_hasSig (hTr.geo.hW.sig w)
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  have hV1 : IsUnit (Γ.V'.J.map Bs.τ₁).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hV
    apply (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁).injective
    rw [map_zero, ← h0]
    exact RingHom.map_det (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.V'.J
  have hW1 : IsUnit ((Γ.W.J.map Bs.τ₁)ᵀ).det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    apply hW
    apply (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁).injective
    rw [map_zero, ← h0]
    exact RingHom.map_det (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.W.J
  set J' := Γ.V'.J.map Bs.τ₁ with hJ'
  set JWt := (Γ.W.J.map Bs.τ₁)ᵀ with hJWt
  let Mx : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) := -(J'⁻¹ * Y * JWt⁻¹)
  obtain ⟨e₀, he₀⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
  set d : Fv D.host.F Bs.v₁ := Bs.τ₁ (D.sp.cm.sig e₀) - Bs.τ₁ e₀ with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 fun e => he₀ ((Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁).injective e)
  let z : Fv D.host.F Bs.v₁ → AE D.host.F D.host.E := fun t =>
    GlobalTheory.LatVac.liftV Bs.v₁ (-t * Bs.τ₁ e₀ / d) ⊗ₜ[D.host.F] (1 : D.host.E) +
      GlobalTheory.LatVac.liftV Bs.v₁ (t / d) ⊗ₜ[D.host.F] e₀
  have hpi : ∀ (τ : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁) (x : AF D.host.F) (e : D.host.E),
      piW τ (x ⊗ₜ[D.host.F] e) = evFin D.host.F Bs.v₁ x * τ e := fun τ x e => by
    simp only [piW, compFin, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rfl
  have hz0 : ∀ t, piW Bs.τ₁ (z t) = 0 := fun t => by
    simp only [z, map_add (f := _), hpi, GlobalTheory.LatVac.evFin_liftV, map_one]
    field_simp
    ring
  have hz1 : ∀ t, piW (Bs.τ₁.comp D.sp.cm.sig) (z t) = t := fun t => by
    simp only [z, map_add (f := _), hpi, GlobalTheory.LatVac.evFin_liftV, map_one, AlgHom.comp_apply]
    rw [hd] at hd0 ⊢
    field_simp
    ring
  have hzA : ∀ t, At (evFin D.host.F Bs.v₁) (z t) := fun t u hu => by
    simp only [z, smul_add, TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV _ _ u hu, TensorProduct.zero_tmul, add_zero]
  refine ⟨Mx.map z, fun u hu => ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
    exact hzA _ u hu
  · ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply, hz0]
  · unfold coBar
    have hx : (Mx.map z).map (piW (Bs.τ₁.comp D.sp.cm.sig)) = Mx := by
      ext i j
      simp only [Matrix.map_apply, hz1]
    rw [hx]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Mx]
    rw [← hJWt, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hV1, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hW1, Matrix.mul_one]

end GlobalTheory.VacShape
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilPairingEqCmIntegerOfPureType
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.PureHom

section Lift

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

theorem linear_lift_unique (u : HolUnif A L g) (u' : HolUnif A' L' g')
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (h₁ : ∀ v, IsTangent v → ∃! w, u'.IsDiff w v)
    (f : A ⟶ A') [IsMonHom f] {F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)}
    (hF : ∀ z, u'.ex (F z) = u.ex z ≫ f) (hF' : ∀ z, u'.ex (F' z) = u.ex z ≫ f) : F = F' := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
  exact (h₁ _ (HomLinear.isTangent_comp f hv)).unique (HomLinear.isDiff_comp u u' f F hF hv hd)
    (HomLinear.isDiff_comp u u' f F' hF' hv hd)

end Lift

def diagMul {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (s : E) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z k := ty k s * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' c z := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring


open PureTriple in
theorem exists_weilEq_smul_of_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (A B : PAT H (Sp ℂ)) (p q : ℕ), p + q = 1 → (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ q)) → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) := by
  intro E _ _ _ H A B p q hpq hdet f₁ f₂ hf₁ hf₂
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨gA, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨uA, HA, χA, -, hA, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨uB, HB, χB, -, hB, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨D, Pe, F, hp, hq, hP, hF, hE, hact⟩ := exists_datum_period hT hL A hty hdet uA hA
  obtain ⟨-, -, -, -, -, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ uA HA χA hA
  obtain ⟨EfB, hEB, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hB
  obtain ⟨F₁, hF₁, hF₁Λ, -⟩ := HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    f₁ hf₁.isMonHom
  obtain ⟨F₂, hF₂, hF₂Λ, -⟩ := HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    f₂ hf₂.isMonHom
  choose ρB hρB using fun s : 𝓞 E => (HomLinear.exists_linear_of_isMonHom B.t.G B.t.G B.ab B.ab _ _ _ _ uB uB hB1 hB2
    (B.t.act.act s) (B.t.act.hom s)).imp fun _ h => h.1
  let G : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    F.toLinearMap ∘ₗ diagMul ty (s : E) ∘ₗ F.symm.toLinearMap
  have hG : ∀ s z, uA.ex (G s z) = uA.ex z ≫ A.t.act.act s := fun s z => by
    have e := hact s (F.symm z)
    rw [F.apply_symm_apply] at e
    exact e
  have hGP : ∀ s a, G s (F (Pe a)) = F (Pe (s • a)) := fun s a => by
    simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    funext i
    exact (hP.1 s a i).symm
  have hcomm : ∀ (f : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f →
      ∀ Fl : (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ), (∀ z, uB.ex (Fl z) = uA.ex z ≫ f) →
      ∀ s z, Fl (G s z) = ρB s (Fl z) := by
    intro f hf Fl hFl s z
    haveI := hf.isMonHom
    haveI := A.t.act.hom s
    have e := linear_lift_unique uA uB hA2 hB1 (A.t.act.act s ≫ f) (F := Fl ∘ₗ G s) (F' := ρB s ∘ₗ Fl)
      (fun z => by rw [LinearMap.comp_apply, hFl, hG, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, hρB, hFl, hf.comm, Category.assoc])
    exact LinearMap.congr_fun e z
  have hadj : ∀ s z w, hermForm HB (ρB s z) w = hermForm HB z (ρB (H.bar s) w) := fun a =>
    (weilEq_iff_hermForm_eq hT hL B.pol B.pol B.pol B.pol uB uB uB uB HB HB χB χB hB hB (B.t.act.act a) (𝟙 _) (𝟙 _)
      (B.t.act.act (H.bar a)) (ρB a) LinearMap.id LinearMap.id (ρB (H.bar a)) (hρB a)
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm) (hρB _)).1
      (weilEq_of_lamEq hL ℂ B.pol B.pol B.pol B.pol _ _ _ _ (B.t.act.hom a) inferInstance inferInstance
        (B.t.act.hom _) (by
          unfold LamEq
          rw [Category.comp_id, Category.comp_id]
          exact B.t.adj a))
  have mem₁ : ∀ a, F₁ (F (Pe a)) ∈ uB.Λ := fun a => hF₁Λ _ ((hF _).2 ⟨a, rfl⟩)
  have mem₂ : ∀ a, F₂ (F (Pe a)) ∈ uB.Λ := fun a => hF₂Λ _ ((hF _).2 ⟨a, rfl⟩)
  let β : D.La → D.La → ℤ := fun a b => EfB ⟨_, mem₁ a⟩ ⟨_, mem₂ b⟩
  have hβ : ∀ a b, (β a b : ℝ) = (hermForm HB (F₁ (F (Pe a))) (F₂ (F (Pe b)))).im := fun a b => hEB _ _
  have hadd₁ : ∀ x y z, β (x + y) z = β x z + β y z := fun x y z => by
    have e : (⟨_, mem₁ (x + y)⟩ : uB.Λ) = ⟨_, mem₁ x⟩ + ⟨_, mem₁ y⟩ := Subtype.ext (by simp)
    show EfB _ _ = EfB _ _ + EfB _ _
    rw [e, map_add (f := _), LinearMap.add_apply]
  have hadd₂ : ∀ x y z, β x (y + z) = β x y + β x z := fun x y z => by
    have e : (⟨_, mem₂ (y + z)⟩ : uB.Λ) = ⟨_, mem₂ y⟩ + ⟨_, mem₂ z⟩ := Subtype.ext (by simp)
    show EfB _ _ = EfB _ _ + EfB _ _
    rw [e, map_add (f := _)]
  have hadjβ : ∀ (s : 𝓞 E) x y, β (s • x) y = β x (H.bar s • y) := fun s x y => by
    have e : (β (s • x) y : ℝ) = β x (H.bar s • y) := by
      rw [hβ, hβ, ← hGP, ← hGP, hcomm f₁ hf₁ F₁ hF₁, hcomm f₂ hf₂ F₂ hF₂, hadj]
    exact_mod_cast e
  obtain ⟨γ, hγ, hβγ⟩ := _root_.GlobalTheory.GramAdj.exists_endo_of_adjoint E H D β hadd₁ hadd₂ hadjβ
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_smul_of_rank_one' E H D (by rw [hp, hq]; exact hpq) γ hγ
  refine ⟨c, (weilEq_iff_hermForm_eq hT hL A.pol A.pol B.pol A.pol uA uA uB uA HB HA χB χA hB hA f₁ f₂
    (A.t.act.act c) (𝟙 _) F₁ F₂ (G c) LinearMap.id hF₁ hF₂ (hG c) (fun _ => (Category.comp_id _).symm)).2 ?_⟩
  refine HermWeil.hermForm_eq_of_im HB HA F₁ F₂ (G c) LinearMap.id uA.full uA.full fun z hz w hw => ?_
  obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 ((hF (F.symm z)).1 (by rwa [F.apply_symm_apply]))
  obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 ((hF (F.symm w)).1 (by rwa [F.apply_symm_apply]))
  have ez : z = F (Pe a) := by rw [ha, F.apply_symm_apply]
  have ew : w = F (Pe b) := by rw [hb, F.apply_symm_apply]
  subst ez ew
  rw [← hβ, hβγ, hc, ← hE, LinearMap.id_apply, hGP]

end GlobalTheory.CM.PureHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlOfOpenLevelInduction
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.LeviSliceTwo


set_option maxHeartbeats 1000000 in
theorem secondSlice_mem_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ V₂ : Submodule ℂ (GA E (a - r) → ℂ), FiniteDimensional ℂ V₂ ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ m₁ : GA E r, (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∈ V₂ := by
  intro E _ _ _ a hind L hL W hW X hX N r hr0 hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨L', W', hL', hW', hA⟩ := _root_.GlobalTheory.HCFct.slice2_autForm E a L hL W hW X hX N r hr0 hr μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨X', D, hX', hB⟩ := _root_.GlobalTheory.SliceTwoCentre.sliceTwoCentre E a L hL W hW X hX N r hr0 hr μ 𝓕 hμ h𝓕 h1 t κ
  have hfin := hind (a - r) (by omega)
  haveI := hfin L' hL' W' hW' X' hX' D
  refine ⟨(Submodule.span ℂ (GlobalTheory.HCF.formsGL E (a - r) L' W' X' D)).map (Sm E (a - r)).subtype, inferInstance, ?_⟩
  intro φ hφ m₁
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨ψ, hψ, hleft, hlev, hkfin, hgr, hL'ψ, hW'ψ⟩ := hA φ hφ m₁
    obtain ⟨hU, hUD, hchar⟩ := hB φ hφ m₁ ψ hψ
    have hAψ : IsAutForm ψ := ⟨hleft, hlev, hkfin, hU, hgr⟩
    have hdec := _root_.GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit (Sm E (a - r)) (Zalg E (a - r))
      (fun x hx y hy => (GlobalTheory.AutGrowth.KilledFin.Zalg_commute hx hy).eq) X' D ψ hU hUD hchar
    refine ⟨ψ, Submodule.span_mono ?_ hdec, hψ⟩
    rintro ψ' ⟨hψ'U, χ, hχ, hnil⟩
    obtain ⟨e1, e2, e3⟩ := _root_.GlobalTheory.CentreInherit.centre_preserves_forms E (a - r) hfin L' W' ψ hAψ hL'ψ hW'ψ ψ' hψ'U
    exact ⟨e1, e2, e3, χ, hχ, hnil⟩
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    funext m₂
    simp only [Submodule.coe_subtype, ZeroMemClass.coe_zero, Pi.zero_apply, integral_zero]
  | add x y hx hy ihx ihy =>
    have hint : ∀ z ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ h,
        IntegrableOn (fun x => z.1 (unip x * h)) 𝓕 μ := by
      intro z hz h
      have hP : Continuous z.1 ∧ (∀ γ h, z.1 (ratGL E a γ * h) = z.1 h) := by
        induction hz using Submodule.span_induction with
        | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left⟩
        | zero => exact ⟨continuous_const, fun _ _ => rfl⟩
        | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2 γ h) (hy.2 γ h)⟩
        | smul c x _ hx => exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2 γ h)⟩
      haveI := hμ
      exact CuspidalL2GL.integrableOn_unip hP.1 hP.2 μ h𝓕 h
    obtain ⟨u, hu, eu⟩ := ihx
    obtain ⟨v, hv, ev⟩ := ihy
    refine ⟨u + v, add_mem hu hv, ?_⟩
    funext m₂
    have eu₂ := congrFun eu m₂
    have ev₂ := congrFun ev m₂
    simp only [Submodule.coe_subtype, Submodule.coe_add, Pi.add_apply] at *
    rw [integral_add (hint x hx _) (hint y hy _)]
    exact congrArg₂ (· + ·) eu₂ ev₂
  | smul c x hx ihx =>
    obtain ⟨u, hu, eu⟩ := ihx
    refine ⟨c • u, Submodule.smul_mem _ c hu, ?_⟩
    funext m₂
    have := congrFun eu m₂
    simp only [Submodule.coe_subtype, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at *
    rw [integral_const_mul, this]

end GlobalTheory.LeviSliceTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormAtPlace

theorem evFin_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  intro F E _ _ _ _ _ v x
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let e := Module.finBasis F E
  let b := Algebra.TensorProduct.basis (AF F) e
  let b' := Algebra.TensorProduct.basis (Fv F v) e
  have hrepr : ∀ (z : AF F ⊗[F] E) i, b'.repr (compFin F E v z) i = evFin F v (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      simp only [compFin, b, b', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]
  have hb : ∀ j, compFin F E v (b j) = b' j := by
    intro j
    simp [compFin, b, b', Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b' (compFin F E v x) = (Algebra.leftMulMatrix b x).map (evFin F v) := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hrepr]
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b, hmat]
  exact AlgHom.map_det (evFin F v) (Algebra.leftMulMatrix b x)

end GlobalTheory.NormAtPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.FourierLocBij

def toCircle {k : Type} [AddMonoid k] (ψ : AddChar k ℂ) (hn : ∀ t, ‖ψ t‖ = 1) : AddChar k Circle where
  toFun t := ⟨ψ t, by simp [Submonoid.unitSphere, hn t]⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (AddChar.map_add_eq_mul ψ a b)

theorem coe_toCircle {k : Type} [AddMonoid k] (ψ : AddChar k ℂ) (hn : ∀ t, ‖ψ t‖ = 1) (t : k) :
    ((toCircle ψ hn t : Circle) : ℂ) = ψ t := rfl

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem translate_fourier [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) {κ : Type} [Fintype κ]
    (m : Measure (κ → k)) [m.IsAddRightInvariant] (φ : (κ → k) → ℂ) (a y : κ → k) :
    ∫ x, φ (x + a) * (ψ (x ⬝ᵥ y) : ℂ) ∂m = (ψ (-(a ⬝ᵥ y)) : ℂ) * ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
  rw [← integral_add_right_eq_self (μ := m) (fun x => φ (x + a) * (ψ (x ⬝ᵥ y) : ℂ)) (-a), ← integral_const_mul]
  congr 1
  funext x
  rw [neg_add_cancel_right, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, neg_dotProduct]
  ring

theorem bijOn_circle [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (μ : Measure (κ → k)) [μ.IsAddHaarMeasure] :
    Set.BijOn (fun (φ : (κ → k) → ℂ) (y : κ → k) => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ)
      (SB (κ → k) : Set _) (SB (κ → k) : Set _) := by
  classical
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ := (GlobalTheory.SplitWeil.selfDual_measure k ψ hc h1).1
  haveI := hν.1
  set m : Measure (κ → k) := Measure.pi fun _ => ν with hm
  have hμ : μ = μ.addHaarScalarFactor m • m := Measure.isAddLeftInvariant_eq_smul μ m
  set r := μ.addHaarScalarFactor m with hr_def
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact NeZero.ne μ hμ
  have hT : ∀ φ : (κ → k) → ℂ, (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) =
      fun y => ((r : ℝ) : ℂ) * ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
    intro φ
    funext y
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have key := fun φ hφ => GlobalTheory.SplitWeil.FourierPi.fourier_pi k κ ψ hc h1 ν hν φ hφ
  have hcomp : ∀ (e : (κ → k) ≃ₜ (κ → k)), ∀ f ∈ SB (κ → k), (fun x => f (e x)) ∈ SB (κ → k) :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  refine ⟨fun φ hφ => ?_, fun φ₁ h₁ φ₂ h₂ he => ?_, fun g hg => ?_⟩
  · show (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (κ → k)
    rw [hT]
    exact Submodule.smul_mem _ ((r : ℝ) : ℂ) (key φ hφ).1
  · have he' : ∀ y, ∫ x, φ₁ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m = ∫ x, φ₂ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
      intro y
      have := congrFun he y
      simp only at this
      rw [hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def,
        Complex.real_smul, Complex.real_smul] at this
      exact mul_left_cancel₀ hr' this
    funext a
    have h1a := (key _ (hcomp (Homeomorph.addRight a) _ h₁)).2
    have h2a := (key _ (hcomp (Homeomorph.addRight a) _ h₂)).2
    simp only [Homeomorph.coe_addRight, zero_add] at h1a h2a
    rw [← h1a, ← h2a]
    congr 1
    funext y
    rw [translate_fourier, translate_fourier, he']
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.SplitWeil.FourierSurj.hat_surjective k κ ψ hc h1 ν hν).2 ⟨g, hg⟩
    refine ⟨((r : ℝ) : ℂ)⁻¹ • Φ.1, Submodule.smul_mem _ _ Φ.2, ?_⟩
    simp only
    rw [hT]
    funext y
    have hΦ' : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ.1 = g := hΦ
    rw [← hΦ']
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hr', one_mul]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, dotProduct_comm y]
    rfl

end General

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourier_bijOn : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    Set.BijOn (fun (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) => ∫ x, φ x * ψ (x ⬝ᵥ y) ∂μ)
      (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := by
  intro F _ _ v ψ hc hn h1 κ _ inst _ μ _
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have e : inst = MeasurableSpace.pi := by
    rw [BorelSpace.measurable_eq (α := κ → Fv F v)]
    exact (BorelSpace.measurable_eq (α := κ → Fv F v) (self := Pi.borelSpace)).symm
  subst e
  have hcont : Continuous (toCircle ψ hn) := Continuous.subtype_mk hc _
  have hne : toCircle ψ hn ≠ 1 := by
    intro h
    apply h1
    ext t
    simpa [coe_toCircle] using congrArg (fun χ : AddChar (Fv F v) Circle => ((χ t : Circle) : ℂ)) h
  exact bijOn_circle (toCircle ψ hn) hcont hne κ μ

end GlobalTheory.FourierLocBij
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentConjugationSignStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_idempotent_conjugation_sign : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∃ f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f ∧ f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
      f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧ piW t f = 1 ∧ piW (t.comp σ) f = -1 := by
  first | exact @GlobalTheory.SwapAtSplit.exists_swap_elt | exact GlobalTheory.SwapAtSplit.exists_swap_elt | (intros; apply GlobalTheory.SwapAtSplit.exists_swap_elt <;> assumption)
end

