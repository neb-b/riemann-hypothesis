module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.PhaseBreaksTargetParts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBoxBoundedValuation
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineToAbelianVarietyConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineConst
open Polynomial

theorem projLine_map_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (f₀ f₁ : Sp (Polynomial k) ⟶ B.left), f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f₀ = spMap b.toRingHom ≫ f₀ := by
  intro k _ _ B _ hB f₀ f₁ h0 h1 h01 a b
  have := hB.proper
  haveI hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let pt : Sp k := IsLocalRing.closedPoint k
  let e : B.left := (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left pt
  obtain ⟨_, ⟨W, hW, rfl⟩, heW, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ e) isOpen_univ
  let L := Localization.Away (X : Polynomial k)
  let t : L := algebraMap (Polynomial k) L X
  let ti : L := IsLocalization.Away.invSelf (X : Polynomial k)
  have hti : t * ti = 1 := IsLocalization.Away.mul_invSelf (X : Polynomial k)
  let g₀ := famMap B f₀ h0 L t
  let g₁ := famMap B f₁ h1 L ti
  have hc := _root_.GlobalTheory.LineConst.famMap_loc_eq B f₀ f₁ h0 h1 h01 L t ti hti
  let V : Set (Sp L) := {τ | ∀ x : Sp (Polynomial L), spMap (algebraMap L (Polynomial L)) x = τ → g₀ x ∈ W ∧ g₁ x ∈ W}
  have hV : IsOpen V := GlobalTheory.T.isOpen_setOf_fibre_charts_mem L _ g₀ g₁ hc W

  have hfib : ∀ (χ : L →ₐ[k] k) (x' : Sp (Polynomial k)),
      spMap (algebraMap L (Polynomial L)) (spMap (Polynomial.mapRingHom (χ : L →+* k)) x') = spMap χ.toRingHom pt := by
    intro χ x'
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.mapRingHom (χ : L →+* k)).comp (algebraMap L (Polynomial L)) =
        (algebraMap k (Polynomial k)).comp (χ : L →+* k) := by
      ext z; simp [Polynomial.algebraMap_apply]
    rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Scheme.Hom.comp_apply]
    congr 1
    exact hsub.elim _ _
  have hW₀ : ∀ χ : L →ₐ[k] k, spMap χ.toRingHom pt ∈ V →
      (∀ x', famMap B f₀ h0 k (χ t) x' ∈ W) ∧ (∀ x', famMap B f₁ h1 k (χ ti) x' ∈ W) := by
    intro χ hχ
    constructor
    · intro x'
      rw [← famMap_base B f₀ h0 χ t, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).1
    · intro x'
      rw [← famMap_base B f₁ h1 χ ti, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).2
  have hinW : ∀ R : Type, ∀ _ : CommRing R, ∀ _ : Algebra k R, ∀ (f : Sp (Polynomial k) ⟶ B.left)
      (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (x : Sp (Polynomial R)), famMap B f hf R 1 x ∈ W := by
    intro R _ _ f hf x
    rw [famMap_one, Scheme.Hom.comp_apply]
    have hx : (spMap (algebraMap k (Polynomial R))) x = pt := hsub.elim _ _
    rw [hx]
    exact heW

  let χ₁ : L →ₐ[k] k := IsLocalization.liftAlgHom (M := Submonoid.powers (X : Polynomial k))
    (f := Polynomial.aeval (1 : k)) (by
      rintro ⟨_, n, rfl⟩
      simp)
  have hχ₁t : χ₁ t = 1 := by simp [χ₁, t]
  have hχ₁ti : χ₁ ti = 1 := by
    have := congrArg χ₁ hti
    rw [map_mul, hχ₁t, _root_.one_mul, map_one] at this
    exact this
  have h1V : spMap χ₁.toRingHom pt ∈ V := by
    intro x hx
    obtain ⟨x', rfl⟩ := _root_.GlobalTheory.fibre_line_over_surjection L k χ₁.toRingHom
      (fun z => ⟨algebraMap k L z, by simp⟩) x hx
    constructor
    · have := famMap_base B f₀ h0 χ₁ t
      rw [hχ₁t] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₀ h0 x'
    · have := famMap_base B f₁ h1 χ₁ ti
      rw [hχ₁ti] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₁ h1 x'
  have hF := _root_.GlobalTheory.punctured_line_open_cofinite k V hV χ₁ h1V
  set F := {c : k | c ≠ 0 ∧ ∀ χ : L →ₐ[k] k, χ (algebraMap (Polynomial k) _ X) = c → spMap χ.toRingHom pt ∉ V}

  have hscale : ∀ c : k, c ≠ 0 → c ∉ F → ∀ a : k,
      spMap (Polynomial.evalRingHom (c * a)) ≫ f₀ = spMap (Polynomial.evalRingHom a) ≫ f₀ := by
    intro c hc0 hcF
    simp only [F, Set.mem_setOf_eq, not_and, not_forall, not_not] at hcF
    obtain ⟨χ, hχt, hχV⟩ := hcF hc0
    obtain ⟨hA, hB'⟩ := hW₀ χ hχV
    have hu : χ t * χ ti = 1 := by rw [← map_mul, hti, map_one]
    have hcmp := _root_.GlobalTheory.LineConst.famMap_loc_eq B f₀ f₁ h0 h1 h01 k (χ t) (χ ti) hu
    have key := GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq k B.left W hW _ _ hA hB' hcmp
    have := scale_inv_of_famMap B f₀ h0 (χ t) key
    simpa [t, hχt] using this
  have hunit : ∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f₀ = spMap (Polynomial.evalRingHom 1) ≫ f₀ := by
    intro c hc
    have hfin : ((F ∪ {0}) ∪ (fun d => c / d) '' F).Finite :=
      (hF.union (Set.finite_singleton 0)).union (hF.image _)
    obtain ⟨d, hd⟩ := hfin.infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_image, not_or, not_exists,
      not_and] at hd
    obtain ⟨⟨hdF, hd0⟩, hd'⟩ := hd
    have hcd0 : c / d ≠ 0 := div_ne_zero hc hd0
    have hcdF : c / d ∉ F := fun h => hd' (c / d) h (by field_simp)
    have e1 := hscale d hd0 hdF (c / d * 1)
    have e2 := hscale (c / d) hcd0 hcdF 1
    rw [_root_.mul_one] at e1 e2
    rw [show d * (c / d) = c by field_simp] at e1
    rw [e1, e2]
  exact _root_.GlobalTheory.ConstAffineLine.eq_of_const_nonzero k B.left B.hom f₀ h0 hunit a b

end GlobalTheory.LineConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspaces
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar


set_option maxHeartbeats 2000000 in
theorem readings_scale_core : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : ℂ), GlobalTheory.Hk3.Core R F → IsStdChar D R.ψ (-1) → GlobalTheory.ConjScalar.ConjScalarAt R → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) → ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ (σ : D.what₂.LL →+* ℂ) (a : Pl D.host.E → List ℤ → D.what₂.LL), ∃ l : ℝ, ∀ x x' y y', GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' → ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
  intro hH hCR D G _ _ Pl0 T0 A T _ R κ v₀ O F ph hC hψ hS fw hbar hio hU hpins i hom ℓ Z hHz hE hZ
  obtain ⟨gramR, c0R, c0L, tie⟩ := hC.fam.tie
  obtain ⟨hex, hconj, hbarσ⟩ := hCR D G Pl0 T0 A T R F κ v₀ O ph (GlobalTheory.Core5.of_core hC) hψ fw hbar hio hU hpins i hom
  have hph : ph ≠ 0 := by
    intro h0
    have h1 : ‖ph‖ = 1 := hom.2.1.2.2.2.2.1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hcore : GlobalTheory.Hk3.Core R F := hC
  have key : ∀ σ : D.what₂.LL →+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → ∀ a : Pl D.host.E → List ℤ → D.what₂.LL, ∃ l : ℝ, ∀ x x' y y',
      GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' →
      ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
    intro σ hσ a
    have hCA := hconj gramR c0R c0L tie σ hσ
    obtain ⟨μ', η', c, c₁, H, j, th, hD⟩ := hCA.2.1
    have hyp : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' := by
      obtain ⟨-, -, u, U, z, ζ, -, -, -, hall⟩ := hCA
      exact (hall μ' η' c c₁ H j th hD).1
    obtain ⟨ev, hev⟩ := GlobalTheory.T.conjugateDatumLift_jointEigenspace_into_one_part hH R F hcore gramR c0R c0L tie i σ c c₁ H j hσ μ' η' th hD hyp (fun P d => σ (a P d))
    obtain ⟨l, hl⟩ := hS gramR c0R c0L tie i σ hσ μ' η' c c₁ H j th hD ev
    refine ⟨l, fun x x' y y' hx hy hy' => ?_⟩
    have hE' := eigF_conj R hC.models.jV gramR c0R c0L tie i σ c c₁ H j hD.2.2.1 a _ hx
    have hp := hev _ hE'
    have hperp := conjForms_mem_orthogonal_ker R hC.models hU gramR c0R c0L tie i σ c c₁ H j μ' η' th ph hph hex hCA hD ℓ Z hHz hE hZ x
    have hadj := adjoint_apply_of_orthogonal_ker th hperp (hl _ hp)
    refine (GlobalTheory.ConjLiftCounterexample.gram_of_conjAt hCA hD hy hy').trans ?_
    refine (inner_apply_of_adjoint_eq th hadj _).trans ?_
    rw [GlobalTheory.LiftLower.inner_conjForms_eq_csumAt R hC.models.jV gramR c0R c0L tie i σ c c₁ H j hD.2.2.1]
    rfl
  intro σ a
  by_cases hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ
  · exact key σ hσ a
  · obtain ⟨hσ', hbar'⟩ := hbarσ σ hσ
    obtain ⟨l, hl⟩ := key _ hσ' a
    refine ⟨l, fun x x' y y' hx hy hy' => ?_⟩
    rw [hbar' y y', hl x x' y y' hx hy hy', map_mul, Complex.conj_ofReal, conj_csumAt]

end GlobalTheory.ConjScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotent
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RatLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem col_coeff {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {g : GAd σ J}
    (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) (j : Fin r) :
    ∃ c : Fin r → AF F ⊗[F] E, (∀ i, j ≤ i → c i = 0) ∧
      (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j = (adMat F X)ᵀ j + adMat F X *ᵥ c := by
  have h := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  obtain ⟨l, hl, e⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 h
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra hne
    obtain ⟨k, -, hik, hkj⟩ := hl (Finsupp.mem_support_iff.2 hne)
    exact absurd (hik.trans_lt hkj) (not_lt.2 hi)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun i a => a • (adMat F X)ᵀ i) (fun i => zero_smul _ _)] at e
    beta_reduce at e
    have e2 : adMat F X *ᵥ ⇑l = ∑ i, l i • (adMat F X)ᵀ i := by
      rw [Matrix.mulVec_eq_sum]; simp only [op_smul_eq_smul]
    rw [e2, e, add_sub_cancel]


omit [NumberField E] in
theorem par_of_unip {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {s : ℕ} (hs : s ≤ r) {d : Fin s → ℕ}
    (hd : Monotone d) {g : GAd σ J} (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) :
    ∃ B : Matrix (Fin s) (Fin s) (AF F ⊗[F] E), B.BlockTriangular d ∧
      (matHom _ σ J g).1 * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B := by
  choose c hc hce using col_coeff hg
  refine ⟨1 + Matrix.of fun i j => c (Fin.castLE hs j) (Fin.castLE hs i), fun i j hlt => ?_, ?_⟩
  · have hji : j < i := not_le.1 fun h => absurd hlt (not_lt.2 (hd h))
    have hle : Fin.castLE hs j ≤ Fin.castLE hs i := by
      rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hji.le
    simp [Matrix.one_apply_ne hji.ne', hc _ _ hle]
  · ext k j
    have h1 := congrFun (hce (Fin.castLE hs j)) k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply] at h1
    rw [Matrix.mul_apply, Matrix.mul_add, Matrix.add_apply, Matrix.mul_one, Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.of_apply] at h1 ⊢
    rw [h1]
    congr 1
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) (fun i => rfl)
    have : s ≤ i.val := by
      by_contra hlt
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    rw [hc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castLE]; omega), mul_zero]

end GlobalTheory.RatLevi

theorem GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S T : Finset (Fin r), S ⊆ T → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T →
        ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y S ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X S, γ = m * ν := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S T _ γ hγ hγT
  obtain ⟨s, hsdef⟩ : ∃ s, s = S.sup fun k => k.val + 1 := ⟨_, rfl⟩
  have hs : s ≤ r := hsdef ▸ Finset.sup_le fun k _ => k.2
  have hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k := fun i => by
    rw [hsdef, Finset.lt_sup_iff]
    exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega
  obtain ⟨d, hddef⟩ : ∃ d : Fin s → ℕ, ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card := ⟨fun i => (S.filter (· < Fin.castLE hs i)).card, fun _ => rfl⟩
  have hdm : Monotone d := fun i j hij => by
    rw [hddef, hddef]
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, lt_of_lt_of_le hk.2 ?_⟩
    rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hij
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS d hddef
  have hp : γ⁻¹ ∈ parFlag σ J (X.submatrix id (Fin.castLE hs)) d :=
    ⟨GlobalTheory.RatLevi.par_of_unip hs hdm (inv_mem hγT), by rw [inv_inv]; exact GlobalTheory.RatLevi.par_of_unip hs hdm hγT⟩
  obtain ⟨u, huF, m, hmF, hpm, hr⟩ := (_root_.GlobalTheory.LeviFlag.levi_decomposition F E σ h n J hJ s (X.submatrix id (Fin.castLE hs))
    (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).1 _ hp
  refine ⟨m⁻¹, inv_mem (hr (inv_mem hγ)), by rw [hl]; exact inv_mem hmF, u⁻¹, by rw [hu]; exact inv_mem huF, ?_⟩
  rw [← inv_inv γ, hpm, mul_inv_rev]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRankDeficientReduction
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), ∃ Φ₀ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Φ₀ Y = 0) ∧
      Φ - Φ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} := by
  intro k _ _ _ _ a d _ ν β _ hν ϖ hϖ hνϖ Φ hΦ
  have key : ∀ r ≤ a, Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ)) ⊔
      GlobalTheory.RankCoinv.twistSpan ν β := by
    intro r hr
    induction r with
    | zero => exact Submodule.mem_sup_left ⟨hΦ, fun Y hY => absurd hY (Nat.not_lt_zero _)⟩
    | succ r ih =>
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (ih (by omega))
      have := _root_.GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank k (Fin a) (Fin d) ϖ hϖ ν β hν hνϖ r (by simpa using hr) x hx
      exact Submodule.add_mem _ this (Submodule.mem_sup_right hy)
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (key a le_rfl)
  refine ⟨x, hx.1, fun Y hY => hx.2 Y (lt_of_le_of_ne (by simpa using Y.rank_le_card_height) hY), ?_⟩
  have e : Φ - x = y := by rw [← hxy]; abel
  rw [e]; exact hy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem spec_localInjective_cancel_left (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
    (φ : R →+* R') [IsLocalHom φ] (hφ : Function.Injective φ) (Y : Scheme.{0}) (a a' : Sp R ⟶ Y)
    (h : spMap φ ≫ a = spMap φ ≫ a') : a = a' := by
  obtain ⟨hcomp, -, -, hloc, hext, -, -⟩ := _root_.GlobalTheory.Nef.evAt_calculus
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint φ
  have hy : a (IsLocalRing.closedPoint R) = a' (IsLocalRing.closedPoint R) := by
    have := congrArg (fun f : Sp R' ⟶ Y => f (IsLocalRing.closedPoint R')) h
    exact (congrArg a hc).symm.trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
      (this.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg a' hc))))
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := a (IsLocalRing.closedPoint R))
    (U := ⊤) trivial
  have h1 : ⊤ ≤ a ⁻¹ᵁ U := (hloc R Y a U).2 hyU
  have h2 : ⊤ ≤ a' ⁻¹ᵁ U := (hloc R Y a' U).2 (hy ▸ hyU)
  have h1' : ⊤ ≤ (spMap φ ≫ a) ⁻¹ᵁ U := (hloc R' Y _ U).2 (((Scheme.Hom.comp_apply _ _ _).trans (congrArg a hc)) ▸ hyU)
  have h2' : ⊤ ≤ (spMap φ ≫ a') ⁻¹ᵁ U := h ▸ h1'
  have key : ∀ (b b' : Sp R' ⟶ Y) (_ : b = b') (hb : ⊤ ≤ b ⁻¹ᵁ U) (hb' : ⊤ ≤ b' ⁻¹ᵁ U),
      evAt b hb = evAt b' hb' := by
    rintro b _ rfl _ _; rfl
  refine hext R Y a a' U hU h1 h2 (RingHom.ext fun f => hφ ?_)
  rw [← hcomp R R' Y φ a U h1 h1' f, ← hcomp R R' Y φ a' U h2 h2' f, key _ _ h h1' h2']

theorem spec_injective_cancel_left_of_separated (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : Function.Injective φ)
    (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y) (hp : a ≫ p = a' ≫ p)
    (h : spMap φ ≫ a = spMap φ ≫ a') : a = a' := by
  let d : Sp R ⟶ pullback p p := pullback.lift a a' hp
  have e1 : a = d ≫ pullback.fst p p := (pullback.lift_fst _ _ _).symm
  have e2 : a' = d ≫ pullback.snd p p := (pullback.lift_snd _ _ _).symm
  let i : pullback d (pullback.diagonal p) ⟶ Sp R := pullback.fst _ _
  have hfac : spMap φ ≫ d = (spMap φ ≫ a) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · rw [Category.assoc, ← e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, ← e2, Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
  let g : Sp R' ⟶ pullback d (pullback.diagonal p) := pullback.lift (spMap φ) (spMap φ ≫ a) hfac
  have hg : g ≫ i = spMap φ := pullback.lift_fst _ _ _
  have key : (spMap φ).appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality]; simp
  have h2 : Function.Injective (spMap φ).appTop := by
    rw [key]
    exact ((Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.injective.comp hφ).comp
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
  have hinj : Function.Injective i.appTop := by
    rw [← hg, Scheme.Hom.comp_appTop] at h2
    exact Function.Injective.of_comp h2
  have : IsIso i := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  have hd : d = inv i ≫ pullback.snd _ _ ≫ pullback.diagonal p := by
    rw [← pullback.condition]; simp [i]
  rw [e1, e2, hd]; simp

theorem spMap_injective_cancel : (∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ], Function.Injective φ → ∀ (Y : Scheme.{0}) (a a' : Sp R ⟶ Y), spMap φ ≫ a = spMap φ ≫ a' → a = a') ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R'), Function.Injective φ → ∀ (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y), a ≫ p = a' ≫ p → spMap φ ≫ a = spMap φ ≫ a' → a = a') :=
  ⟨fun R R' _ _ _ _ φ _ hφ Y a a' h => spec_localInjective_cancel_left R R' φ hφ Y a a' h,
    fun R R' _ _ φ hφ S Y p _ a a' hp h => spec_injective_cancel_left_of_separated R R' φ hφ S Y p a a' hp h⟩

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureOfValuationRing
section
set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.WeilIntegral


set_option autoImplicit false in
open scoped TensorProduct in
theorem _root_.GlobalTheory.WeilIntegral.isAlgebraic_of_etale (S B : Type) [CommRing S] [IsDomain S] [CommRing B] [Algebra S B]
    [Algebra.Etale S B] (f : B) : IsAlgebraic S f := by
  classical
  let K := FractionRing S
  haveI : Algebra.Etale K (TensorProduct S K B) := Algebra.Etale.baseChange S B K
  haveI : Module.Finite K (TensorProduct S K B) :=
    Algebra.FormallyUnramified.finite_of_free K (TensorProduct S K B)
  haveI hal : Algebra.IsAlgebraic K (TensorProduct S K B) := Algebra.IsAlgebraic.of_finite K _
  obtain ⟨p, hp0, hp⟩ := hal.isAlgebraic ((1 : K) ⊗ₜ[S] f)
  set q := IsLocalization.integerNormalization (nonZeroDivisors S) p
  have hq0 : q ≠ 0 := fun h0 =>
    hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h0)
  have hq : Polynomial.aeval ((1 : K) ⊗ₜ[S] f) q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ p hp
  have hmap : (1 : K) ⊗ₜ[S] Polynomial.aeval f q = 0 := by
    rw [← hq, ← Algebra.TensorProduct.includeRight_apply, ← Polynomial.aeval_algHom_apply]
    rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K B 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).2 (TensorProduct.isBaseChange S B K)
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors S) (TensorProduct.mk S K B 1)).1 hmap
  refine ⟨Polynomial.C (s : S) * q, ?_, ?_⟩
  · exact mul_ne_zero (Polynomial.C_ne_zero.2 (nonZeroDivisors.coe_ne_zero s)) hq0
  · rw [map_mul, Polynomial.aeval_C, ← Algebra.smul_def]
    exact hs

end GlobalTheory.WeilIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def SquareTriple (W : G.Weil) (t : T) (i j : ℕ) : Prop :=
  ∀ M : Vol G, M.Is t → ∃ (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _) (om' : _),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' ∧
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁

theorem SquareTriple.of_forall {W : G.Weil} {t : T} {i j : ℕ} (h : SquareTriple W t i j) {M : Vol G} (hM : M.Is t) :
    ∃ (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _) (om' : _),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' ∧
      ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁ := h M hM

end GlobalTheory.FunObj

end
end

