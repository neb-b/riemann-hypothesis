module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDarbouxOperatorsLeviAndDouble
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU
open GlobalTheory.AdelicSvN GlobalTheory.AdelicSvNLevi

namespace GlobalTheory.TowU.LeviModel

variable {F : Type} [Field F] [NumberField F]

theorem isOp_levi (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : IsUnit A.det) :
    IsOp ψ (AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) (compM A⁻¹) (compM A) := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix ι ι (AF F) := A.map (algebraMap F (AF F))
  let Aim : Matrix ι ι (AF F) := A⁻¹.map (algebraMap F (AF F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine
    { pres := comp_mem A⁻¹ A h2 h1
      pres' := comp_mem A A⁻¹ h1 h2
      left := fun φ _ => funext fun x => ?_
      right := fun φ _ => funext fun x => ?_
      adm := fun l hl g hg => ?_
      adm' := fun l hl g hg => ?_
      Heisenberg₂ := fun w φ _ => funext fun x => ?_
      theta := ⟨1, one_ne_zero, fun φ _ => ?_⟩
      norm := fun μ μ' hμ hμ' => ?_ }
  · change φ (Aim *ᵥ (Am *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  · change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A A⁻¹ h1 h2).continuous,
      hg.2.comp_homeomorph (finHomeo A A⁻¹ h1 h2)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A A⁻¹ h1 h2)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A A⁻¹ h1 h2, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  · rw [one_mul]
    unfold thetaSum
    let e : (ι → F) ≃ (ι → F) :=
      { toFun := fun ξ => A⁻¹ *ᵥ ξ
        invFun := fun ξ => A *ᵥ ξ
        left_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
        right_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] }
    have he := Equiv.tsum_eq e (fun ξ : ι → F => φ fun i => algebraMap F (AF F) (ξ i))
    refine Eq.trans (tsum_congr fun ξ => ?_) he
    change φ (Aim *ᵥ _) = φ (fun i => algebraMap F (AF F) ((A⁻¹ *ᵥ ξ) i))
    congr 1
    funext i
    exact (RingHom.map_mulVec (algebraMap F (AF F)) A⁻¹ ξ i).symm
  · haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    letI : MeasurableSpace (ι → AF F) := borel _
    haveI : BorelSpace (ι → AF F) := ⟨rfl⟩
    let L : (ι → AF F) ≃+ (ι → AF F) :=
      { toFun := fun x => Aim *ᵥ x
        invFun := fun x => Am *ᵥ x
        left_inv := fun x => by simp only [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
        right_inv := fun x => by simp only [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
        map_add' := fun x y => Matrix.mulVec_add _ _ _ }
    have hc : Continuous L := continuous_const.matrix_mulVec continuous_id
    have hc' : Continuous L.symm := continuous_const.matrix_mulVec continuous_id
    let H : (ι → AF F) ≃ₜ (ι → AF F) := { toEquiv := L.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
    haveI : (Measure.map L μ').IsAddHaarMeasure := L.isAddHaarMeasure_map μ' hc hc'
    have e := Measure.isAddLeftInvariant_eq_smul (Measure.map L μ') μ
    refine ⟨Measure.addHaarScalarFactor (Measure.map L μ') μ, ?_, ENNReal.coe_ne_top, fun φ _ => ?_⟩
    · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (Measure.map L μ') μ).ne'
    · have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) H.toMeasurableEquiv (μ := μ')
      change ∫⁻ x, ‖φ (Aim *ᵥ x)‖ₑ ^ 2 ∂μ' = _
      have hL : (Measure.map H.toMeasurableEquiv μ') = Measure.map L μ' := rfl
      rw [hL, e, lintegral_smul_measure] at hm
      exact hm.symm.trans rfl

theorem inv_diag {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A 0 0 A)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul A hA]
  simp [Matrix.fromBlocks_one]

theorem dblAct_levi {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : IsUnit A.det) :
    dblAct (AdelicSvN.act (R := AF F) (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) =
      AdelicSvN.act (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 A) 0 0 (Matrix.fromBlocks A 0 0 A)⁻¹ᵀ) := by
  funext w
  rw [inv_diag A hA, act_levi, Matrix.fromBlocks_transpose]
  simp only [dblAct, act_levi, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, add_zero, zero_add, Matrix.transpose_zero, Matrix.mulVec_neg, neg_neg]

theorem isOp2_levi (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : IsUnit A.det) :
    IsOp2 ψ (AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) (compM A⁻¹) (compM A) := by
  have hA2 : IsUnit (Matrix.fromBlocks A 0 0 A).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hA
  refine ⟨isOp_levi ψ A hA, compM (Matrix.fromBlocks A 0 0 A)⁻¹, compM (Matrix.fromBlocks A 0 0 A), ?_,
    fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_levi A hA]; exact isOp_levi ψ _ hA2
  · funext x
    rw [inv_diag A hA]
    change boxFun φ₁ φ₂ _ = φ₁ _ * star (star (φ₂ _))
    rw [star_star]
    simp only [boxFun, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec, add_zero, zero_add]
    rfl

end GlobalTheory.TowU.LeviModel


open GlobalTheory.TowU.LeviModel in
theorem GlobalTheory.TowU.realised_levi2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ A : Matrix κ κ F, IsUnit A.det →
    ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
      IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) S S' :=
  fun _ _ _ ψ _ _ _ _ A hA => ⟨_, _, isOp2_levi ψ A hA⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTorusEquivariantOrthonormalFrames
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.TorusExt

open ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem value_indep (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ)
    (hF : ∀ y, IsUnitFr X y → ∀ c ∈ Bor X.Ψ r, IsUnitFr X (rmul y c) → F (rmul y c) = bchar la c * F y)
    {y y' b b' : Frame X.Ψ r} (hy : IsUnitFr X y) (hy' : IsUnitFr X y') (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r)
    (h : rmul y b = rmul y' b') : bchar la b * F y = bchar la b' * F y' := by
  have hi := ExtFPf.invF_mem X hb'
  have hc := ExtFPf.mul_mem X hb hi
  have e : rmul y (rmul b (ExtFPf.invF X b')) = y' := by
    rw [← ExtFPf.rmul_assoc, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb', ExtFPf.rmul_oneF]
  have h1 := hF y hy _ hc (by rw [e]; exact hy')
  rw [e, ExtFPf.bchar_mul X la hb hi] at h1
  have h2 : bchar la b' * bchar la (ExtFPf.invF X b') = 1 := by
    rw [← ExtFPf.bchar_mul X la hb' hi, ExtFPf.rmul_invF X hb', ExtFPf.bchar_oneF]
  rw [h1]
  linear_combination (-(bchar la b * F y)) * h2

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), (∀ y, IsUnitFr X y → ∀ t : X.Ψ → Fin r → ℝ, F (rmul y (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) = bchar la (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) * F y) → ∃ Q : Frame X.Ψ r → ℂ, (∀ y, IsUnitFr X y → Q y = F y) ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x := by
  intro E _ _ _ r X la F hF
  obtain ⟨-, hex, huniq, -⟩ := _root_.GlobalTheory.FlagGS.gram_schmidt_frames E r X
  have hF' : ∀ y, IsUnitFr X y → ∀ c ∈ Bor X.Ψ r, IsUnitFr X (rmul y c) → F (rmul y c) = bchar la c * F y := by
    intro y hy c hc hyc
    obtain ⟨t, rfl⟩ := huniq y hy c hc hyc
    exact hF y hy t
  let D : Frame X.Ψ r → Prop := fun x => ∃ p : Frame X.Ψ r × Frame X.Ψ r,
    IsUnitFr X p.1 ∧ p.2 ∈ Bor X.Ψ r ∧ x = rmul p.1 p.2
  let Q : Frame X.Ψ r → ℂ := fun x => if h : D x then bchar la h.choose.2 * F h.choose.1 else 0
  have hQ : ∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, Q (rmul y b) = bchar la b * F y := by
    intro y hy b hb
    have hD : D (rmul y b) := ⟨(y, b), hy, hb, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hD.choose_spec
    show (if h : D (rmul y b) then bchar la h.choose.2 * F h.choose.1 else 0) = _
    rw [dite_eq_left hD]
    exact (value_indep X la F hF' hy h1 hb h2 h3).symm
  refine ⟨Q, fun y hy => ?_, fun x hx b hb => ?_⟩
  · have := hQ y hy _ (ExtFPf.oneF_mem X)
    rwa [ExtFPf.rmul_oneF, ExtFPf.bchar_oneF, one_mul] at this
  · obtain ⟨y, hy, c, hc, rfl⟩ := hex x hx
    rw [ExtFPf.rmul_assoc, hQ y hy _ (ExtFPf.mul_mem X hc hb), hQ y hy c hc, ExtFPf.bchar_mul X la hc hb]
    ring

end GlobalTheory.HolRead.TorusExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupRightActionComponents
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompAct

open ReciprocityTheory.ChartRestriction.G.FD

theorem exists_action {H G C : Type} [Group H] [Group G] (comp : H → C) (hs : ∀ x, ∃ h, comp h = x)
    (Lift : G → H → Prop) (hex : ∀ g, ∃ k, Lift g k) (h1 : Lift 1 1)
    (hmul : ∀ g g' k k', Lift g k → Lift g' k' → Lift (g * g') (k * k'))
    (key : ∀ g k k' h h', Lift g k → Lift g k' → comp h = comp h' → comp (h * k) = comp (h' * k')) :
    ∃ mv : C → G → C, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, comp h = x) ∧
      ∀ g k, Lift g k → ∀ h, comp (h * k) = mv (comp h) g := by
  choose rep hrep using hs
  choose l hl using hex
  have main : ∀ g k, Lift g k → ∀ h, comp (h * k) = comp (rep (comp h) * l g) :=
    fun g k hk h => key g k (l g) h _ hk (hl g) (hrep _).symm
  refine ⟨fun x g => comp (rep x * l g), fun x => ?_, fun x g g' => ?_, fun x => ⟨rep x, hrep x⟩, main⟩
  · have := main 1 1 h1 (rep x)
    rw [mul_one, hrep] at this
    exact this.symm
  · show comp (rep x * l (g * g')) = comp (rep (comp (rep x * l g)) * l g')
    rw [← main g' (l g') (hl g'), mul_assoc]
    exact key (g * g') _ _ _ _ (hl _) (hmul _ _ _ _ (hl g) (hl g')) rfl

theorem frame_calc {n : Type} [Fintype n] [DecidableEq n] (x B P Q P' M : Matrix n n ℂ) (hy : (B * x).det ≠ 0)
    (h1 : M * B = B * Q) (h2 : P * Q = P') : P * x * ((B * x)⁻¹ * M * (B * x)) = P' * x := by
  have hx : IsUnit x.det := by
    rw [Matrix.det_mul] at hy
    exact (right_ne_zero_of_mul hy).isUnit
  have e : M * (B * x) = (B * x) * (x⁻¹ * (Q * x)) := by
    rw [← Matrix.mul_assoc M, h1, Matrix.mul_assoc B x, Matrix.mul_nonsing_inv_cancel_left _ _ hx, Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ M, e, Matrix.nonsing_inv_mul_cancel_left _ _ hy.isUnit, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hx, ← Matrix.mul_assoc, h2]

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem archM_mul (V : HSp D) (hr : V.rank = r) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ g) * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ g') =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (g * g')) := by
  have e : archM V θ (g * g') = archM V θ g * archM V θ g' := by
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  rw [e]
  exact Matrix.submatrix_mul_equiv (archM V θ g) (archM V θ g') _ (finCongr hr).symm _

theorem coset_of_comp_eq {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hf : ∀ h, ∃ p : GA D V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) p) * x₀ τ.1)
    {h h' : GA D V} (e : (dict h).1 = (dict h').1) :
    ∃ a ∈ GinfC V, ∃ γ ∈ GQ V, ∃ k ∈ Kf, h * a = γ * h' * k := by
  obtain ⟨-, -, ⟨x0, h0, h3⟩, -, -, h6⟩ := hd
  have hf' : ∀ g c x, dict g = ⟨c, x⟩ → ∃ p : GA D V, ∀ τ : (X c).Ψ, mat x τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) p) * x₀ τ.1 := by
    intro g c x hg
    have := hf g
    rw [hg] at this
    exact this
  have h6' : ∀ g g' c x, dict g = ⟨c, x⟩ → (∃ γ' ∈ (X c).Γ, dict g' = ⟨c, lact γ' x⟩) →
      ∃ γ ∈ GQ V, ∃ k ∈ Kf, g' = γ * g * k := by
    intro g g' c x hg hh
    refine h6 g g' ?_
    rw [hg]
    exact hh
  obtain ⟨x', hx'⟩ : ∃ x' : Frame (X (dict h).1).Ψ r, dict h' = ⟨(dict h).1, x'⟩ := by
    generalize (dict h).1 = c at e
    subst e
    exact ⟨_, rfl⟩
  obtain ⟨hdom, g0, hg0⟩ := h0 (dict h).1
  obtain ⟨b, hb⟩ := hf' _ _ _ hg0
  obtain ⟨p, hp⟩ := hf h
  obtain ⟨p', hp'⟩ := hf' _ _ _ hx'
  obtain ⟨a, a1, a2⟩ := GlobalTheory.UnitarySplit.ga_glue V _ 1 (GlobalTheory.UnitarySplit.infHom_mem V (b * (p⁻¹ * p') * b⁻¹)) (one_mem _)
  obtain ⟨γ', hγ', he⟩ := h3 h a a2
  refine ⟨a, a2, h6' h' _ _ x' hx' ⟨γ', hγ', he.trans ?_⟩⟩
  congr 2
  funext τ
  have ha : archM V (th (dict h).1 τ) a = archM V (th (dict h).1 τ) (b * (p⁻¹ * p') * b⁻¹) := by
    unfold archM
    rw [a1]
  show (mat (dict h).2 τ * ((mat (x0 (dict h).1) τ)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr)
    (archM V (th (dict h).1 τ) a) * mat (x0 (dict h).1) τ) : Matrix (Fin r) (Fin r) ℂ) = mat x' τ
  have hy := (hdom τ).1
  rw [hb τ] at hy
  rw [hp τ, hp' τ, hb τ, ha]
  refine frame_calc _ _ _ (Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (p⁻¹ * p'))) _ _ hy ?_ ?_
  · rw [archM_mul, archM_mul, inv_mul_cancel_right]
  · rw [archM_mul, mul_inv_cancel_left]

theorem comm_real_fin (V : HSp D) {a k : GA D V} (ha : a ∈ GinfC V) (hk : k ∈ GfC V) : a * k = k * a := by
  refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
  · rw [map_mul, map_mul, show infHom V k = 1 from hk, mul_one, one_mul]
  · rw [map_mul, map_mul, show finHom V a = 1 from ha, mul_one, one_mul]

theorem exists_action_dict {V W : HSp D} (hV : V = W) {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hf : ∀ h, ∃ p : GA D V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) p) * x₀ τ.1)
    (β : GL (Fin W.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ W.rank) {G : Type} [Group G] (eG : G →* G0 L.Pg L.r)
    (hK : ∀ k : GA D W, Lev.IsLevelLift W β L 1 k ↔ cast (congrArg (GA D) hV.symm) k ∈ Kf)
    (hex : ∀ g, ∃ k, Lev.IsLevelLift W β L (eG g) k) :
    ∃ mv : Comp → G → Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧
      (∀ x, ∃ h, (castDict hV dict h).1 = x) ∧ ∀ g k, Lev.IsLevelLift W β L (eG g) k →
        ∀ h, (castDict hV dict (h * k)).1 = mv (castDict hV dict h).1 g := by
  subst hV
  have hK' : ∀ k : GA D V, Lev.IsLevelLift V β L 1 k ↔ k ∈ Kf := hK
  refine exists_action (fun h => (dict h).1) (fun x => ?_) (fun g k => Lev.IsLevelLift V β L (eG g) k) hex ?_ ?_ ?_
  · obtain ⟨x0, h0, -⟩ := hd.2.2.1
    obtain ⟨g, hg⟩ := (h0 x).2
    exact ⟨g, congrArg Sigma.fst hg⟩
  · show Lev.IsLevelLift V β L (eG 1) 1
    rw [map_one]
    exact (hK' 1).2 (one_mem _)
  · intro g g' k k' hk hk'
    show Lev.IsLevelLift V β L (eG (g * g')) (k * k')
    rw [map_mul]
    exact GlobalTheory.ProjComm.isLift_mul hk hk'
  · intro g k k' h h' hk hk' e
    obtain ⟨a, ha, γ, hγ, k0, hk0, he⟩ := coset_of_comp_eq hd x₀ hf e
    have h1 := GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_inv hk') ((hK' k0).2 hk0)) hk
    rw [mul_one, inv_mul_cancel] at h1
    have h2 : h * k * a = γ * (h' * k' * (k'⁻¹ * k0 * k)) := by
      rw [mul_assoc h, ← comm_real_fin V ha hk.1, ← mul_assoc h, he]
      group
    obtain ⟨x0, -, h3⟩ := hd.2.2.1
    obtain ⟨_, -, e1⟩ := h3 (h * k) a ha
    obtain ⟨_, -, e2⟩ := hd.1 γ hγ (h' * k' * (k'⁻¹ * k0 * k))
    obtain ⟨_, -, e3⟩ := hd.2.1 _ ((hK' _).1 h1) (h' * k')
    have f1 := congrArg Sigma.fst e1
    have f2 := congrArg Sigma.fst e2
    have f3 := congrArg Sigma.fst e3
    rw [h2] at f1
    exact f1.symm.trans (f2.trans f3)


set_option maxHeartbeats 1000000 in
theorem exists_action_components : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → ∃ mv : (T.U ((i : ℕ) + 1) σ).Comp → G → (T.U ((i : ℕ) + 1) σ).Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 = x) ∧ ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = mv (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 g := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hR ht hpb i σ hσ hV hex
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨th, hr, hth, hd⟩ := ht.laws.dictU _ hj σ hσ
  obtain ⟨hr', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := ht.laws.adPin _ hj σ hσ
  have e' : th' = th := funext fun k => funext fun τ => GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth' k τ) (hth k τ)
  subst e'
  exact exists_action_dict hV hd (T.x₀ _ σ) (fun h => (hL h).elim fun γ hγ => ⟨γ * h, hγ.2.2.2⟩)
    (R.βW i) (R.datWp i R.triv) R.eG.toMonoidHom (_root_.GlobalTheory.LiftLevel.isLift_one_iff_mem_level T R κ v₀ hR ht hpb i σ hσ hV) hex

end GlobalTheory.CompAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealLatticeLineCoefficients
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem latticeLine_fractionalIdeal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  intro E _ _ n L hL x hx
  let f : E →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)
  have hf : Function.Injective f := by
    intro a b h
    have h' : a • x = b • x := h
    exact smul_left_injective E hx h'
  have hLfg : L.FG := hL.fg
  have hmapfg : ((L.comap f).map f).FG :=
    Submodule.FG.of_le hLfg (Submodule.map_comap_le f L)
  have hS : (L.comap f).FG := Submodule.fg_of_fg_map_injective f hf hmapfg
  exact ⟨⟨L.comap f, FractionalIdeal.isFractional_of_fg hS⟩, fun s => Iff.rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusLiftStalk
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem frobLift_stalk (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U)
    (F₀ : Γ(Y, U) →+* Γ(Y, U)) (hp2 : (p : Γ(Y, U)) ^ 2 = 0) (hF₀ : ∀ z, ∃ w, F₀ z = z ^ p + p * w)
    (y : Y) (hy : y ∈ U) :
    ∃ F : Y.presheaf.stalk y →+* Y.presheaf.stalk y,
      (∀ b, F ((Y.presheaf.germ U y hy).hom b) = (Y.presheaf.germ U y hy).hom (F₀ b)) ∧
        ∀ z, ∃ w, F z = z ^ p + p * w := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact frobLift_localization p (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl F₀ hp2 hF₀

theorem stalk_ringHom_ext {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U)
    {C : Type} [CommRing C] (f f' : Y.presheaf.stalk y →+* C)
    (h : ∀ b, f ((Y.presheaf.germ U y hy).hom b) = f' ((Y.presheaf.germ U y hy).hom b)) : f = f' := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact IsLocalization.ringHom_ext (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (RingHom.ext h)

theorem exists_frobLift_stalk_of_etCoord :
    ∀ (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (g : Y ⟶ Sp (ZMod (p ^ 2))) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (η : Y) (hη : η ∈ U), ∃ F : Y.presheaf.stalk η →+* Y.presheaf.stalk η, (∀ z, ∃ w, F z = z ^ p + p * w) ∧ (∀ l, F ((Y.presheaf.germ U η hη).hom (t l)) = (Y.presheaf.germ U η hη).hom (t l) ^ p) ∧ ∀ (y : Y), y ∈ U → ∀ (h : η ⤳ y), ∀ z ∈ stalkIm h, ∃ w ∈ stalkIm h, F z = z ^ p + p * w := by
  intro p _ Y g U n t hU ht η hη
  obtain ⟨F₀, hF₀, hFt⟩ := frob_lift_etale_chart p _ ht
  have hp2 : (p : Γ(Y, U)) ^ 2 = 0 := by
    have h := map_natCast (cstOn g U) (p ^ 2)
    rw [ZMod.natCast_self, map_zero] at h
    rw [← Nat.cast_pow, ← h]
  obtain ⟨F, hFg, hF⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ η hη
  refine ⟨F, hF, fun l => ?_, fun y hy h z hz => ?_⟩
  · have := hFt l
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    rw [hFg, this, map_pow]
  · obtain ⟨F', hFg', hF'⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ y hy
    have hs : ∀ b, (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.germ U y hy).hom b) =
        (Y.presheaf.germ U η hη).hom b := fun b =>
      congrArg (fun k => k.hom b) (Y.presheaf.germ_stalkSpecializes hy h)
    have hc : F.comp (Y.presheaf.stalkSpecializes h).hom =
        (Y.presheaf.stalkSpecializes h).hom.comp F' := by
      apply stalk_ringHom_ext U hU y hy
      intro b
      rw [RingHom.comp_apply, RingHom.comp_apply, hs, hFg, hFg', hs]
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨w, hw⟩ := hF' a
    refine ⟨_, ⟨w, rfl⟩, ?_⟩
    have := congrArg (· a) hc
    simp only [RingHom.comp_apply] at this
    rw [this, hw, map_add (f := _), map_mul, map_pow, map_natCast]

end GlobalTheory.DI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_fixed_vector_of_type_occurring_in_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∃ v ∈ (principalLevelFrame.FinTyp.conjT π).S, v ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v ∧ ∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v := by
  first | exact @GlobalTheory.OccRowVec.exists_vec_of_occRows | exact GlobalTheory.OccRowVec.exists_vec_of_occRows | (intros; apply GlobalTheory.OccRowVec.exists_vec_of_occRows <;> assumption)
end

