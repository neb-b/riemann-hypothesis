module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZero
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSFull

theorem eq_lieComb {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ} {cf : Fin n → R}
    {v : Fin n → (epsR R ⟶ A)} {w : epsR R ⟶ A} (h : IsLieComb cf v w) : w = GlobalTheory.FlagTan.lieComb cf v := by
  obtain ⟨u, hu, rfl⟩ := h
  unfold GlobalTheory.FlagTan.lieComb
  congr 2
  funext i
  exact Over.OverMorphism.ext (hu i)

theorem eq_one_of_isLieComb_zero {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {v : Fin n → (epsR R ⟶ A)} (hv : ∀ i, IsTangent (v i)) {w : epsR R ⟶ A}
    (h : IsLieComb (fun _ => (0 : R)) v w) : w = 1 := by
  rw [eq_lieComb h]
  unfold GlobalTheory.FlagTan.lieComb
  simp [GlobalTheory.GrpTangent.epsScale_zero_comp (hv _)]

theorem isKSValue_one_sum {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} {h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i} {J : Type} (s : Finset J)
    (c : J → K) (F : J → HdR A) (hF : ∀ k, IsKSValue h (F k) 1) : IsKSValue h (∑ k ∈ s, c k • F k) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, ⟨0, zero_mem _, fun _ => (LinearMap.zero_apply _).trans (by simp)⟩, isLieImage_one_iff.2 (zero_mem _)⟩
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    have := ((hF k).smul (c k)).add ih
    rwa [MonObj.comp_one, _root_.mul_one] at this

theorem isKSValue_one_of_rows {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (HdR A))
    (hiso : ∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) (hlag : ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A)
    (hperf : LinearMap.IsPerfPair ψ) (halt : ψ.IsAlt)
    (hsym : ∀ f g k k', IsFilLift h f k → IsFilLift h g k' → ψ f k' + ψ k g = 0)
    {Ι : Type} [Fintype Ι] {m : Ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A)
    (hl : ∀ k, IsLieImage (hb k) (ub k.1 k.2)) (hspan : Submodule.span K (Set.range hb) ⊔ Fil A = ⊤)
    (P : Ι → Prop) (cj : Ι → Ι) (hcj : ∀ σ, P σ → ¬ P (cj σ))
    (h0 : ∀ k : (Σ σ, Fin (m σ)), ¬ P k.1 → GlobalTheory.FlagTan.IsKSRow h ψ hb k 1)
    (h1 : ∀ k : (Σ σ, Fin (m σ)), P k.1 → ∃ cf w, IsLieComb cf (ub (cj k.1)) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb k w) :
    ∀ f ∈ Fil A, IsKSValue h f 1 := by
  classical

  have what₂ : ∀ k : (Σ σ, Fin (m σ)), ∃ f ∈ Fil A, (∀ k', ψ f (hb k') = if k' = k then 1 else 0) ∧
      ∃ kf, IsFilLift h f kf ∧ (¬ P k.1 → kf ∈ Fil A) ∧
        (P k.1 → ∃ cf : Fin (m (cj k.1)) → K, kf - ∑ b, cf b • hb ⟨cj k.1, b⟩ ∈ Fil A) := fun k => by
    by_cases hk : P k.1
    · obtain ⟨cf, w, hc, f, hf, hd, kf, hkf, hw⟩ := h1 k hk
      refine ⟨f, hf, fun k' => (hd k').trans (ite_congr rfl (fun _ => rfl) (fun _ => rfl)), kf, hkf,
        fun h' => absurd hk h', fun _ => ⟨cf, ?_⟩⟩
      have e := GlobalTheory.FlagTan.isLieImage_lieComb cf (fun b => hl ⟨cj k.1, b⟩)
      rw [← eq_lieComb hc] at e
      exact hw.sub_mem e
    · obtain ⟨f, hf, hd, kf, hkf, hw⟩ := h0 k hk
      exact ⟨f, hf, fun k' => (hd k').trans (ite_congr rfl (fun _ => rfl) (fun _ => rfl)), kf, hkf,
        fun _ => isLieImage_one_iff.1 hw, fun h' => absurd h' hk⟩
  choose F hF hδ kf hkf hk0 hk1 using what₂

  have zero : ∀ d ∈ Fil A, (∀ k, ψ d (hb k) = 0) → d = 0 := fun d hd h0 => by
    have hker : Submodule.span K (Set.range hb) ⊔ Fil A ≤ LinearMap.ker (ψ d) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso d hd g hg
      rintro _ ⟨k, rfl⟩
      exact h0 k
    have e : ψ d = 0 := LinearMap.ext fun x => hker (hspan ▸ Submodule.mem_top)
    exact hperf.bijective_left.1 (e.trans (map_zero ψ).symm)

  have span : ∀ g ∈ Fil A, g = ∑ k, ψ g (hb k) • F k := fun g hg => by
    refine (sub_eq_zero.1 (zero _ (sub_mem hg (sum_mem fun k _ => Submodule.smul_mem _ _ (hF k))) fun k' => ?_))
    have e : ∑ k, (ψ (ψ g (hb k) • F k)) (hb k') = ψ g (hb k') := by
      rw [Finset.sum_eq_single k' (fun b _ hb' => by
        rw [map_smul, LinearMap.smul_apply, hδ, if_neg (Ne.symm hb'), smul_zero]) (by simp)]
      rw [map_smul, LinearMap.smul_apply, hδ, if_pos rfl, smul_eq_mul, _root_.mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, e, sub_self]

  have key : ∀ k k', ψ (kf k) (F k') = 0 := fun k k' => by
    by_cases hk : P k.1
    · by_cases hk' : P k'.1
      · obtain ⟨cf, hcf⟩ := hk1 k hk
        have e1 := hiso _ hcf _ (hF k')
        rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1
        set_option synthInstance.maxHeartbeats 100000 in
          rw [e1, map_sum, LinearMap.sum_apply]
        refine Finset.sum_eq_zero fun b _ => ?_
        have hne : (⟨cj k.1, b⟩ : Σ σ, Fin (m σ)) ≠ k' := fun e => hcj _ hk (by subst e; exact hk')
        rw [map_smul, LinearMap.smul_apply, ← LinearMap.IsAlt.neg halt (F k') _, hδ, if_neg hne, neg_zero,
          smul_zero]
      · have e1 := hsym _ _ _ _ (hkf k) (hkf k')
        rw [hiso _ (hF k) _ (hk0 k' hk'), zero_add] at e1
        exact e1
    · exact hiso _ (hk0 k hk) _ (hF k')
  have hone : ∀ k, IsKSValue h (F k) 1 := fun k =>
    ⟨kf k, hkf k, isLieImage_one_iff.2 (hlag _ fun g hg => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [span g hg, map_sum]
      exact Finset.sum_eq_zero fun k' _ => by rw [map_smul, key, smul_zero])⟩
  intro f hf
  rw [span f hf]
  exact isKSValue_one_sum _ _ _ hone

end GlobalTheory.KSFull

namespace GlobalTheory.KSFull

theorem conj_embK' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  show conjEmb τ ((H.bar z : 𝓞 E) : E) = τ (z : E)
  rw [H.bar_eq]
  simp [conjEmb, IsCMField.complexEmbedding_complexConj]

theorem ksFull : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧ ∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1 := by
  intro PP E _ _ _ H Dw l Xo c K _ _ y x' _ _ hKS
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hKS
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, hπ, hπ', e, ?_⟩
  have P := PP.p5
  have hU := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  haveI : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc i π', e, ha z]
    · rw [Category.assoc, Category.assoc, Over.w, h.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ₀, hpol₀, hiso, hperf, hlag⟩ := _root_.GlobalTheory.PolExists.polForm_exists P Xo hπ
  obtain rfl : ψ = ψ₀ := IsPolForm.unique P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hpol hpol₀
  have hadj := _root_.GlobalTheory.PolAdjoint.polForm_adjoint P Xo hπ a ha hpol
  have hK := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme P h hA' gA'
  obtain ⟨ub₀, hu₀, ht₀, he₀, hbasis₀⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  obtain rfl : ub = ub₀ := by
    funext σ k
    apply ReciprocityTheory.ChartRestriction.G.PullbackSections.push_inj hπ
    apply Over.OverMorphism.ext
    change (ub σ k).left ≫ π = (ub₀ σ k).left ≫ π
    rw [hu, hu₀]
  have hl' : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), IsLieImage (hb k) (ub k.1 k.2) := fun k => hl k.1 k.2
  obtain ⟨hspan, hind⟩ := _root_.GlobalTheory.LieBasis.lifts_basis_mod_fil P y hπ ub hu hb hl'
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hl' k).push (a.act z)
    rw [he₀] at h1
    exact h1.sub_mem ((hl' k).smul _)
  have hsym := _root_.GlobalTheory.KSSym.ks_symm PP E H Dw l Xo K y.x x' A A' π π' i h ψ hπ hπ' e hpol
  refine isKSValue_one_of_rows h ψ hiso hlag hperf hpol.isAlt hsym ub hb hl' hspan
    (fun σ => σ ∈ GlobalTheory.FlagTan.psiSet H) conjEmb
    (fun σ hσ => ((GlobalTheory.FlagTan.isHalf_psiSet H) σ).1 hσ) ?_ ?_
  ·
    have key : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, j⟩ 1 := fun τ j => by
      obtain ⟨w, hw, hr⟩ := hM τ j
      rwa [eq_one_of_isLieComb_zero (fun b => ht₀ τ.1 b) hw] at hr
    rintro ⟨σ, j⟩ hσ
    have hτ : conjEmb σ ∈ GlobalTheory.FlagTan.psiSet H := by
      rw [(GlobalTheory.FlagTan.isHalf_psiSet H) (conjEmb σ), GlobalTheory.AllWt.conjEmb_conjEmb]
      exact hσ
    suffices ∀ σ' (_ : conjEmb (conjEmb σ) = σ') (j' : Fin (Dw.mult σ')),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨σ', j'⟩ 1 from this σ (GlobalTheory.AllWt.conjEmb_conjEmb σ) j
    intro σ' e'
    subst e'
    exact key ⟨conjEmb σ, hτ⟩
  ·
    rintro ⟨σ, j⟩ -
    exact GlobalTheory.KSExist.ksRow_exists_lieComb h a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => _root_.GlobalTheory.KSExist.isKSValue_act h a a' hc z hw)
      χ ub hb hspan hind heig hbasis₀ (conjEmb σ) σ
      (fun z => by
        simp only [χ, RingHom.comp_apply]
        rw [← conj_embK' c (conjEmb σ) z, GlobalTheory.AllWt.conjEmb_conjEmb]) j

end GlobalTheory.KSFull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotent
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftGroupLaw

theorem exists_grpObj_isAbelianScheme : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∀ (m : X ⊗ X ⟶ X), l ≫ m.left = (μ[A₀]).left ≫ i →
    ∃ _ : GrpObj X, IsGrpPullback A₀ X (spMap π) i ∧ IsAbelianScheme X := by
  intro R R₀ _ _ π hπ hN A₀ _ hA X i hi hsm e he he1 l hl1 hl2 m hm
  haveI : Smooth X.hom := hsm
  haveI : IsCommMonObj A₀ := hA.comm
  obtain ⟨hpX, hgX⟩ := _root_.GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift R R₀ π hπ hN X A₀ i hi hsm hA.proper hA.geomConnected
  haveI := hpX
  haveI := hgX
  have s2 : Smooth (X ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have p2 : IsProper (X ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have g2 : GeometricallyConnected (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _
  haveI := s2
  haveI := p2
  haveI := g2
  have s3 : Smooth ((X ⊗ X) ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have p3 : IsProper ((X ⊗ X) ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have g3 : GeometricallyConnected ((X ⊗ X) ⊗ X).hom := by
    rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _

  obtain ⟨jA, hjl⟩ : ∃ jA : (Over.map (spMap π)).obj A₀ ⟶ X, jA.left = i := ⟨Over.homMk i hi.w, rfl⟩
  obtain ⟨E, hEl⟩ : ∃ E : 𝟙_ (Over (Sp R)) ⟶ X, E.left = e := ⟨Over.homMk e he, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L : (Over.map (spMap π)).obj (A₀ ⊗ A₀) ⟶ X ⊗ X,
      L = lift ((Over.map (spMap π)).map (fst A₀ A₀) ≫ jA) ((Over.map (spMap π)).map (snd A₀ A₀) ≫ jA) := ⟨_, rfl⟩
  have hL : L.left = l := by
    have p : IsPullback (fst X X).left (snd X X).left X.hom X.hom := IsPullback.of_hasPullback _ _
    refine p.hom_ext ?_ ?_
    · rw [← Over.comp_left, hLd, lift_fst, hl1, Over.comp_left, Over.map_map_left, hjl]
    · rw [← Over.comp_left, hLd, lift_snd, hl2, Over.comp_left, Over.map_map_left, hjl]
  have pt : ∀ (T : Over (Sp R₀)) (x y : T ⟶ A₀),
      lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) = (Over.map (spMap π)).map (lift x y) ≫ L := by
    intro T x y
    rw [hLd, comp_lift, ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc, lift_fst, lift_snd]
  have hLm : L ≫ m = (Over.map (spMap π)).map μ[A₀] ≫ jA := by
    ext1; rw [Over.comp_left, hL, hm, Over.comp_left, Over.map_map_left, hjl]
  have ptm : ∀ (T : Over (Sp R₀)) (x y : T ⟶ A₀),
      lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) ≫ m = (Over.map (spMap π)).map (x * y) ≫ jA := by
    intro T x y
    rw [pt, Category.assoc, hLm, ← CategoryTheory.Functor.map_comp_assoc, Hom.mul_def]
  have hE : ∀ T : Over (Sp R₀), (Over.map (spMap π)).map (1 : T ⟶ A₀) ≫ jA = toUnit _ ≫ E := by
    intro T
    have h1 : (1 : T ⟶ A₀) = (Over.homMk T.hom (Category.comp_id T.hom) : T ⟶ Over.mk (𝟙 (Sp R₀))) ≫ 1 := (comp_one _).symm
    ext1
    rw [Over.comp_left, Over.comp_left, Over.map_map_left, h1, Over.comp_left, Category.assoc, hjl, he1,
      Over.toUnit_left, Over.map_obj_hom, hEl]
    rfl
  have hj : (Over.map (spMap π)).map (𝟙 A₀) ≫ jA = jA := by rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hjE : jA ≫ toUnit X ≫ E = (Over.map (spMap π)).map (1 : A₀ ⟶ A₀) ≫ jA := by
    rw [hE, comp_toUnit_assoc]

  obtain ⟨τ, hτd⟩ : ∃ τ : X ⟶ X, τ = lift (toUnit X ≫ E) (𝟙 X) ≫ m := ⟨_, rfl⟩
  have hτ : jA ≫ τ = jA := by
    rw [hτd, comp_lift_assoc, Category.comp_id, hjE]
    have h := ptm A₀ 1 (𝟙 A₀)
    rw [hj, _root_.one_mul, hj] at h
    exact h
  have τiso : IsIso τ := by
    refine _root_.GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction R R₀ π hπ hN X X A₀ A₀ i i hi hi inferInstance τ (𝟙 A₀) ?_ inferInstance
    have h := congrArg (fun g => g.left) hτ
    simp only [Over.comp_left, hjl] at h
    rw [h, Over.id_left, Category.id_comp]
  obtain ⟨m₁, hm₁d⟩ : ∃ m₁ : X ⊗ X ⟶ X, m₁ = m ≫ inv τ := ⟨_, rfl⟩
  have hjτ : jA ≫ inv τ = jA := by
    conv_lhs => rw [← hτ]
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have ptm₁ : ∀ (T : Over (Sp R₀)) (x y : T ⟶ A₀),
      lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) ≫ m₁ = (Over.map (spMap π)).map (x * y) ≫ jA := by
    intro T x y
    rw [hm₁d, ← Category.assoc, ptm, Category.assoc, hjτ]
  have hLm₁ : L ≫ m₁ = (Over.map (spMap π)).map μ[A₀] ≫ jA := by
    rw [hm₁d, ← Category.assoc, hLm, Category.assoc, hjτ]
  have hm₁ : l ≫ m₁.left = (μ[A₀]).left ≫ i := by
    have h := congrArg (fun g => g.left) hLm₁
    simp only [Over.comp_left, Over.map_map_left, hL, hjl] at h
    exact h
  have one_mul₁ : lift (toUnit X ≫ E) (𝟙 X) ≫ m₁ = 𝟙 X := by
    rw [hm₁d, ← Category.assoc, ← hτd, IsIso.hom_inv_id]
  have hEE : lift E E ≫ m₁ = E := by
    have h := congrArg (fun g => E ≫ g) one_mul₁
    simp only [comp_lift_assoc, Category.comp_id] at h
    rwa [← Category.assoc, toUnit_unique (E ≫ toUnit X) (𝟙 _), Category.id_comp] at h

  have hμ : μ[A₀] = fst A₀ A₀ * snd A₀ A₀ := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have σ₀iso : IsIso (lift (fst A₀ A₀) μ[A₀]) := by
    refine ⟨⟨lift (fst A₀ A₀) ((fst A₀ A₀)⁻¹ * snd A₀ A₀), ?_, ?_⟩⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · rw [Category.assoc, lift_snd, comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, hμ, inv_mul_cancel_left,
          Category.id_comp]
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · rw [Category.assoc, lift_snd, hμ, comp_mul, lift_fst, lift_snd, mul_inv_cancel_left, Category.id_comp]
  have hl₂ : IsPullback l (A₀ ⊗ A₀).hom (X ⊗ X).hom (spMap π) := GlobalTheory.AbDual.isPullback_prod hi hi hl1 hl2
  have hLfst : L ≫ fst X X = (Over.map (spMap π)).map (fst A₀ A₀) ≫ jA := by rw [hLd, lift_fst]
  have hLσ : L ≫ lift (fst X X) m₁ = (Over.map (spMap π)).map (lift (fst A₀ A₀) μ[A₀]) ≫ L := by
    rw [comp_lift, hLm₁, hLfst, ← pt]
  have σiso : IsIso (lift (fst X X) m₁) := by
    refine _root_.GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction R R₀ π hπ hN (X ⊗ X) (X ⊗ X) (A₀ ⊗ A₀) (A₀ ⊗ A₀) l l hl₂ hl₂ inferInstance _ _ ?_ σ₀iso
    have h := congrArg (fun g => g.left) hLσ
    simp only [Over.comp_left, Over.map_map_left, hL] at h
    exact h
  have toLeft : ∀ {P Q : Over (Sp R)} (a : Q ⟶ P) (f f' : P ⟶ X), a ≫ f = a ≫ f' → a.left ≫ f.left = a.left ≫ f'.left :=
    fun a f f' h => by simpa only [Over.comp_left] using congrArg (fun g => g.left) h
  have EXT := _root_.GlobalTheory.ShearLift.eq_of_shear R R₀ π hπ hN A₀ X i hi l hl1 hl2 m₁ hm₁ σiso
  have hEu : toUnit (𝟙_ (Over (Sp R))) = 𝟙 _ := toUnit_unique _ _

  have mul_one₁ : lift (𝟙 X) (toUnit X ≫ E) ≫ m₁ = 𝟙 X := by
    refine EXT X A₀ i hi hsm hpX hgX e he _ _ ?_ ?_
    · rw [← hjl]
      apply toLeft
      rw [comp_lift_assoc, Category.comp_id, hjE]
      have h := ptm₁ A₀ (𝟙 A₀) 1
      rw [hj, _root_.mul_one, hj] at h
      exact h
    · rw [← hEl]
      apply toLeft
      simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, hEu, Category.id_comp, hEE]

  have comm₁ : (β_ X X).hom ≫ m₁ = m₁ := by
    refine EXT (X ⊗ X) (A₀ ⊗ A₀) l hl₂ s2 p2 g2 (lift E E).left (by simpa using Over.w (lift E E)) _ _ ?_ ?_
    · rw [← hL]
      apply toLeft
      rw [hLd, lift_braiding_hom_assoc, ptm₁, ptm₁, _root_.mul_comm]
    · apply toLeft
      rw [lift_braiding_hom_assoc]

  obtain ⟨L₃, hL₃d⟩ : ∃ L₃ : (Over.map (spMap π)).obj ((A₀ ⊗ A₀) ⊗ A₀) ⟶ (X ⊗ X) ⊗ X,
      L₃ = lift (lift ((Over.map (spMap π)).map (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀) ≫ jA)
        ((Over.map (spMap π)).map (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) ≫ jA)) ((Over.map (spMap π)).map (snd (A₀ ⊗ A₀) A₀) ≫ jA) :=
    ⟨_, rfl⟩
  have hL₃1 : L₃ ≫ fst (X ⊗ X) X = (Over.map (spMap π)).map (fst (A₀ ⊗ A₀) A₀) ≫ L := by
    rw [hL₃d, lift_fst, pt, ← comp_lift, lift_fst_snd, Category.comp_id]
  have hL₃2 : L₃ ≫ snd (X ⊗ X) X = (Over.map (spMap π)).map (snd (A₀ ⊗ A₀) A₀) ≫ jA := by
    rw [hL₃d, lift_snd]
  have hk3 : IsPullback L₃.left ((A₀ ⊗ A₀) ⊗ A₀).hom ((X ⊗ X) ⊗ X).hom (spMap π) := by
    refine GlobalTheory.AbDual.isPullback_prod hl₂ hi (h := L₃.left) ?_ ?_
    · rw [← Over.comp_left, hL₃1, Over.comp_left, Over.map_map_left, hL]
    · rw [← Over.comp_left, hL₃2, Over.comp_left, Over.map_map_left, hjl]
  have assoc₁ : (m₁ ▷ X) ≫ m₁ = (α_ X X X).hom ≫ (X ◁ m₁) ≫ m₁ := by
    refine EXT ((X ⊗ X) ⊗ X) ((A₀ ⊗ A₀) ⊗ A₀) L₃.left hk3 s3 p3 g3 (lift (lift E E) E).left
      (by simpa using Over.w (lift (lift E E) E)) _ _ ?_ ?_
    · apply toLeft
      rw [hL₃d]
      simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, ptm₁]
      rw [_root_.mul_assoc]
    · apply toLeft
      simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hEE]

  obtain ⟨iX, hiXd⟩ : ∃ iX : X ⟶ X, iX = lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁) ≫ snd X X := ⟨_, rfl⟩
  have right_inv₁ : lift (𝟙 X) iX ≫ m₁ = toUnit X ≫ E := by
    have hp : (lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁)) ≫ lift (fst X X) m₁ = lift (𝟙 X) (toUnit X ≫ E) := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have h1 : (lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁)) ≫ fst X X = 𝟙 X := by
      have h := congrArg (· ≫ fst X X) hp
      simp only [Category.assoc, lift_fst] at h
      simpa only [Category.assoc] using h
    have h2 : (lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁)) ≫ m₁ = toUnit X ≫ E := by
      have h := congrArg (· ≫ snd X X) hp
      simp only [Category.assoc, lift_snd] at h
      simpa only [Category.assoc] using h
    have h3 : lift (𝟙 X) iX = lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, h1]
      · rw [lift_snd, hiXd, Category.assoc]
    rw [h3, h2]
  have left_inv₁ : lift iX (𝟙 X) ≫ m₁ = toUnit X ≫ E := by
    rw [← comm₁, lift_braiding_hom_assoc, right_inv₁]
  letI G : GrpObj X :=
    { one := E
      mul := m₁
      inv := iX
      one_mul := by
        rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id, ← one_mul₁, ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_one := by
        rw [← cancel_epi (ρ_ X).inv, Iso.inv_hom_id, ← mul_one₁, ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_assoc := assoc₁
      left_inv := left_inv₁
      right_inv := right_inv₁ }
  refine ⟨G, ⟨hi, fun T x y x₀ y₀ hx hy => ?_⟩, ⟨⟨comm₁⟩, hsm, hpX, hgX⟩⟩
  have ex : ∀ (z : T ⟶ A₀) (z₀ : Over.mk (T.hom ≫ spMap π) ⟶ X), z₀.left = z.left ≫ i →
      z₀ = (Over.map (spMap π)).map z ≫ jA := fun z z₀ h => by
    ext1
    rw [h, Over.comp_left, Over.map_map_left, hjl]
  rw [ex x x₀ hx, ex y y₀ hy, Hom.mul_def]
  change (lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) ≫ m₁).left = _
  rw [ptm₁, Over.comp_left, Over.map_map_left, hjl]

end GlobalTheory.LiftGroupLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLieBasisPullbackGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.KeyExtLie

theorem dnRingHom_ext {R S : Type} [CommRing R] [CommRing S] {f f' : DualNumber R →+* S}
    (h1 : ∀ a, f (TrivSqZeroExt.inl a) = f' (TrivSqZeroExt.inl a)) (h2 : f DualNumber.eps = f' DualNumber.eps) : f = f' := by
  refine RingHom.ext fun x => ?_
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * DualNumber.eps := by
    ext <;> simp
  rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, h1, h1, h2]

end GlobalTheory.KeyExtLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponentStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keySection_fourthRoot_perComponent : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ ρ : KeySec Xo c, ∀ Z : Comp Xo c, ∃ a : c.F, a ≠ 0 ∧ idem Z * (ρ.ρ : Rul Xo c) ^ 4 = a • (idem Z * (K : Rul Xo c)) := by
  first | exact @GlobalTheory.KeyRoot.exists_keySec_pow_four | exact GlobalTheory.KeyRoot.exists_keySec_pow_four | (intros; apply GlobalTheory.KeyRoot.exists_keySec_pow_four <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisOfIntegralFramedPointStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), Integral T io y → ∀ (χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y), χ ≫ pullback.snd _ _ = spMap φ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) → ∀ (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n), ∃ v : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt (χ ≫ pullback.fst _ _) ⟶ Y.t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis Y.t.act (χ ≫ pullback.fst _ _) (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (letI := io.toAlgebra; SameVec Y y (y.u τ (Fin.cast hn.symm i)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (v i).left)) := by
  first | exact @GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec | exact GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec | (intros; apply GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec <;> assumption)
end

