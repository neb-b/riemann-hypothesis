module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceCompactTorusClassesCompactWeylCosets
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersAgreeInertUnramified
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertChars

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_mul_of_at {v : Pl (F := F)} {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hy : At (evFin F v) y) :
    y = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.EmbChart.atPlace v 1) * y := by
  have h0 : evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h1 : (1 - GlobalTheory.EmbChart.atPlace v 1) • y = 0 := hy _ h0
  rw [Algebra.smul_def, map_sub, map_one, sub_mul, one_mul, sub_eq_zero] at h1
  exact h1

private lemma tensorProduct_map_eq_zero_of_at_of_atPlace_eq_zero {R : Type} [CommRing R] [Algebra F R] {v : Pl (F := F)} (φ : AF F →ₐ[F] R)
    (hφ : φ (GlobalTheory.EmbChart.atPlace v 1) = 0) {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hy : At (evFin F v) y) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) y = 0 := by
  rw [eq_mul_of_at hy, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul,
    Algebra.algebraMap_self_apply, hφ, TensorProduct.zero_tmul, zero_mul]

theorem eq_ideleAt_of_at {v : Pl (F := F)} (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (hz : At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1)) :
    z = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v z) := by
  have hev : ∀ {R : Type} [CommRing R] [Algebra F R] (φ : AF F →ₐ[F] R), φ (GlobalTheory.EmbChart.atPlace v 1) = 0 →
      Algebra.TensorProduct.map φ (AlgHom.id F E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := by
    intro R _ _ φ hφ
    have h := tensorProduct_map_eq_zero_of_at_of_atPlace_eq_zero φ hφ hz
    rwa [map_sub, map_one, sub_eq_zero] at h
  apply GlobalTheory.Doubling.idele_ext
  · intro w
    rw [GlobalTheory.Doubling.unitInf_ideleAt]
    ext
    refine hev (evInf F w) ?_
    rw [GlobalTheory.EmbChart.atPlace_apply]
    show GlobalTheory.AutFunCompare.evW w (fstA F (pairA F 0 (singleFin v 1))) = 0
    exact map_zero _
  · intro u
    by_cases huv : u = v
    · subst huv
      rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
    · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne huv]
      ext
      refine hev (evFin F u) ?_
      rw [GlobalTheory.EmbChart.atPlace_apply]
      exact evalV_singleFin_ne huv 1

end GlobalTheory.InertChars

namespace GlobalTheory.InertChars

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locIdele_eq_of_inert {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (α β : Chr F E) (hres : ∀ b : (AF F)ˣ, α (ideleMap F E b) = β (ideleMap F E b))
    (hα : UnrAt α w) (hβ : UnrAt β w) (y : (w.adicCompletion E)ˣ) :
    α (locIdele F w y) = β (locIdele F w y) := by
  unfold UnrAt at hα hβ
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  obtain ⟨a, ha⟩ := GlobalTheory.LFun.InertValue.exists_isUnifAt hw h
  have hπ : α (locIdele F w (Units.map (complMap h).toMonoidHom a)) =
      β (locIdele F w (Units.map (complMap h).toMonoidHom a)) := by
    rw [GlobalTheory.LFun.InertValue.locIdele_complMap hw h a]
    exact hres _
  generalize Units.map (complMap h).toMonoidHom a = π at ha hπ
  have hunit : ∀ u : (w.adicCompletion E)ˣ, Valued.v (u : w.adicCompletion E) = 1 →
      α (locIdele F w u) = β (locIdele F w u) := by
    intro u hu
    have h1 : locChar α w u = 1 := hα u hu
    have h2 : locChar β w u = 1 := hβ u hu
    rw [← h2] at h1
    have h3 := congrArg (fun x : ℂˣ => (x : ℂ)) h1
    simp only [locChar, MonoidHom.comp_apply, Circle.toUnits_apply, Units.val_mk0] at h3
    exact Circle.ext h3
  have key : ∀ (u : (w.adicCompletion E)ˣ) (n : ℤ), Valued.v (u : w.adicCompletion E) = 1 →
      α (locIdele F w (u * π ^ n)) = β (locIdele F w (u * π ^ n)) := by
    intro u n hu'
    rw [map_mul, map_mul, map_mul, map_zpow, map_zpow, map_zpow, hunit u hu', hπ]
  have hy0 : Valued.v (y : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (y : w.adicCompletion E) = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hy0).symm⟩
  have hu : Valued.v ((y * π ^ k : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    have hπv : Valued.v (π : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := ha
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπv, hk, ← WithZero.exp_zsmul,
      ← WithZero.exp_add, smul_neg, smul_eq_mul, mul_one, add_neg_cancel, WithZero.exp_zero]
  have hy : y = (y * π ^ k) * π ^ (-k) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hy]
  exact key _ _ hu

theorem beta_eq_alpha_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
      ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → X.β z = X.α z := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv z hz
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have hpow : ((-1 : ℂ)) ^ a = (-1) ^ a' := by
    have he := hT.geo.even
    rw [Nat.even_add] at he
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, (he.mp ha).neg_one_pow]
    · have ha' : Odd a' := Nat.not_even_iff_odd.mp (fun h' => Nat.not_even_iff_odd.mpr ha (he.mpr h'))
      rw [ha.neg_one_pow, ha'.neg_one_pow]
  have hres : ∀ b : (AF F)ˣ, X.β (ideleMap F E b) = X.α (ideleMap F E b) := by
    intro b
    have e1 : ((X.α (ideleMap F E b) : Circle) : ℂ) = _ := hT.chars.resα b
    have e2 : ((X.β (ideleMap F E b) : Circle) : ℂ) = _ := hT.chars.resβ b
    apply Circle.ext
    rw [e1, e2, hpow]
  have hnot : ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl (F := F)))) := by
    rw [h]
    exact hv
  rw [eq_ideleAt_of_at z hz, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw]
  exact locIdele_eq_of_inert hw X.β X.α hres (hT.chars.unrβ w hnot) (hT.chars.unrα w hnot) _

end GlobalTheory.InertChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRealPlaceTorusClassesSignVectors
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section
namespace GlobalTheory.RealSigns

theorem signs_real : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) :=
  of_cosets _root_.GlobalTheory.TrEll.RealClasses.real_classes

end GlobalTheory.RealSigns
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLiftOfCharacterisationClauses
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefModel

theorem exists_coefAt_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ :=
  fun _ _ hR i _ _ _ _ σ hσ => exists_coefAt_of_posDef i (hR.models.vpos i) σ hσ

end GlobalTheory.CoefModel

namespace GlobalTheory.ConjForms


set_option maxHeartbeats 2000000 in
theorem exists_conjForms_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∃ (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i gramR c0R c0L hT σ c c₁ hc
  have h1 := hT.coefL i A.μ0
  obtain ⟨e, -, he, -⟩ := h1
  have hact : ∀ γ : GQ (Vc D i), ∃ T : VsV D i D.what₂.LL → VsV D i D.what₂.LL,
      (∀ v, c0L i (T v) = (R.cV i).coef.ρ γ (c0L i v)) ∧ ∀ v, c₁ (T v) = c.coef.ρ γ (c₁ v) := fun γ =>
    (exists_ratMat (Vc D i) γ).elim fun γE hγ =>
      ⟨rhoVr (labLL D) (lamV D i) γE, (hT.mapL i).1 γ γE hγ, hc.act γ γE hγ⟩
  have h2 := exists_baseChange (W' := c.W) σ c.coef.ρ (R.B.L i A.μ0).pres (c0L i) c₁ e he hact
    (levChar_mem R hC.lev hC.grp.chiW i)
  obtain ⟨H, j, hm, hb⟩ := h2
  refine ⟨H, j, hc.coef, hc.act, hc.indep, hc.span, hc.pair, hm, fun x h => ?_⟩
  exact (hb x h).imp fun v hv => ⟨(congrFun (hC.models.jV i A.μ0 x) h).trans hv.1, hv.2⟩

end GlobalTheory.ConjForms

namespace GlobalTheory.GalLift

theorem conjForms_rescale_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ gramR' c0R' c0L', Comparison₂ R gramR' c0R' c0L' → ∀ (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L' i) c c₁ H j → ∃ c₁' : VsV D i D.what₂.LL →ₛₗ[σ] c.W, IsConjForms R i σ (c0L i) c c₁' H j := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i gramR c0R c0L ht gramR' c0R' c0L' ht' σ c c₁ H j hf
  have h1 := ht.coefL i A.μ0
  have h2 := ht'.coefL i A.μ0
  have m1 := ht.mapL i
  have m2 := ht'.mapL i
  obtain ⟨e, he1, he2, he3, -⟩ := h1
  obtain ⟨e', he1', he2', he3', -⟩ := h2
  have key := rescale_abstract _ (bVV D.what₂.LL (lamV D i)) D.what₂.embLL σ _ (c0L i) (c0L' i) _ _ e e' he1 he1' he2 he2'
    he3 he3' m2.2.1 c₁ hf.indep hf.span hf.pair
  obtain ⟨c₁', k1, k2, k3, k4, k5⟩ := key
  refine ⟨c₁', ⟨hf.coef, fun γ γE hγ => ?_, k1, k2, k3, hf.model, fun x h => ?_⟩⟩
  · exact k5 _ _ _ (m1.1 γ γE hγ) (m2.1 γ γE hγ) (hf.act γ γE hγ)
  · have hb := hf.base x h
    obtain ⟨v', a1, a2⟩ := hb
    have hv := k4 v'
    obtain ⟨v, b1, b2⟩ := hv
    exact ⟨v, a1.trans b1, a2.trans b2⟩

end GlobalTheory.GalLift

namespace GlobalTheory.GalLift.Vec

theorem exists_vecData_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ f₀ f B, VecData R i σ f₀ f B := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ _
  have hθ : IsInfFam R.θ := hC.models.inf
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i A.μ0).std
  have hQ : R.Q A.μ0 = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hC.lev.xi_base]; exact fun _ _ => rfl)
  have h0 := (hC.thP.vP i A.μ0).2
  obtain ⟨e, he, -⟩ := h0
  rw [hQ] at he
  have sdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hc := GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)
  have h1 := GlobalTheory.Member.vacuum_oriented_exists D R.ψ R.θ hψ hθ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ))
    (D.sp.V_sig _) (D.sp.W_sig _) (fun τ => isCartanInv_one (hC.models.BV i τ)) hc _ _ sdV sdW
  obtain ⟨f₀, hf₀⟩ := h1
  have h2 := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) _ _ (R.βV i) (R.βW i)
    R.Pg ∅ (fun _ => 1) sdV sdW (hC.lev.βV i).choose_spec.1 (hC.lev.βW i).choose_spec.1 (Finset.disjoint_empty_right _)
    ⟨e, he⟩ f₀ hf₀
  obtain ⟨f, hf⟩ := h2
  have h3 := fun ρ => exists_isONBasis (hc ρ) (D.sp.W_sig _ (tauE D ρ))
  choose B hB using h3
  have h4 := hf.2
  obtain ⟨e', -, h5⟩ := h4
  exact ⟨f₀, f, B, hf, hB, theta_pureTensorO hψ hθ _ _ _ _ (theta_of_thetaAt hψ hθ h5 hf₀.2.theta)⟩

end GlobalTheory.GalLift.Vec

namespace GlobalTheory.ConjThetaIntegral
open scoped Topology ComplexOrder

theorem exists_isThetaP_conj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ c₀ c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' c₀ c c₁ H j hj ω f₀ f B io hω hv
  have hm := hj.model
  obtain ⟨χ', hχ, hH⟩ := hm
  exact IsThetaP₂ hω (D.sp.V_sig _) (hR.models.vpos i) c hj.coef (R.βV i) (R.datVt i A.μ0) χ'
    (fun k hk => Units.ext (conjVal_one (hχ k) (congrArg Units.val hk))) H.e
    (fun x => hH.2.1.le (LinearMap.mem_range_self _ x))
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f) hv.theta io (hR.models.νV i A.μ0)

end GlobalTheory.ConjThetaIntegral

namespace GlobalTheory.GalLift.ProjLift


set_option maxHeartbeats 1600000 in
theorem exists_isProjOf_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, IsExtVec (R.MW i σ) (fun ρ => v ρ) → (∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) = thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v)) → ∃ th, IsProjOf R i σ thP th := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i gramR c0R c0L hT σ hσ μ' η' c c₁ H j hj ω f₀ f B io thP hL v hv h
  have hspan := GlobalTheory.ConjSpan.span_conjForms R hC.models.jV gramR c0R c0L hT i σ c c₁ H j hj
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (holShape_of_overK R i hσ)
  have he : ∀ τ, v τ ≠ 0 := fun τ h0 => by
    have := (hv τ).1
    simp [h0] at this
  have hex := exists_lift hlow.1 hlow.2 (R.HW i σ).e
    (fun t => (hC.models.HW i σ).2.1.le (LinearMap.mem_range_self _ t)) (thP ∘ₗ (c.ext ∘ₗ H.e).rangeRestrict)
    (fun y => kEquiv_thetaP hL.2.2.1 hL.2.2.2 _) j hspan v he h
  obtain ⟨φ, hφ⟩ := hex
  exact ⟨(∑ g, RealDat.eC (A := A) σ g • R.gW i σ g) ∘ₗ φ, fun x u =>
    (proj_apply R hC.models.gW i σ (φ x) _).trans (congrArg (R.eWf i σ) (hφ x u))⟩

end GlobalTheory.GalLift.ProjLift

namespace GlobalTheory.GalLift

theorem conjLift_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∃ (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype
    G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField
    Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ) (c
    : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∃ (H : HMod (Bridge.Gf
    (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L
    i) c c₁ H j) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ gramR' c0R' c0L', Comparison₂ R gramR' c0R' c0L' → ∀ (σ
    : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H
    : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L'
    i) c c₁ H j → ∃ c₁' : VsV D i D.what₂.LL →ₛₗ[σ] c.W, IsConjForms R i σ (c0L
    i) c c₁' H j) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ f₀ f B, VecData R i σ f₀ f B) ∧ (∀ {D
    : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks
    : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F
    : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE
    D)ˣ →* Circle) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ c₀ c c₁ H j → ∀ (ω : GA D (Vc D
    i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D
    i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i
    σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsWeilDatumO R.ψ (Vc D i) (Wc D
    i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i
    A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ
    H.e)) thP) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D
    i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D
    i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i
    σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ
    H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) →
    ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, IsExtVec (R.MW i
    σ) (fun ρ => v ρ) → (∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) = thP ((c.ext ∘ₗ
    H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v)) → ∃ th, IsProjOf R i σ thP th) :=
  ⟨GlobalTheory.CoefModel.exists_coefAt_five,
   GlobalTheory.ConjForms.exists_conjForms_five,
   GlobalTheory.GalLift.conjForms_rescale_five,
   GlobalTheory.GalLift.Vec.exists_vecData_five,
   GlobalTheory.ConjThetaIntegral.exists_isThetaP_conj_five,
   GlobalTheory.GalLift.ProjLift.exists_isProjOf_five⟩

end GlobalTheory.GalLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
section
noncomputable section

open Formalism.BasicNotions.TH

namespace GlobalTheory.RealLift.Dbl

def dblCol {β : Type} {R S : ℕ} (C : Matrix β (Ix R S) ℂ) : Ix (R + S) (S + R) → β ⊕ β → ℂ
  | .inl p => Sum.elim (fun r => Sum.elim (fun i => C i (.inl r)) (0 : β → ℂ))
      (fun s => Sum.elim (0 : β → ℂ) (fun i => C i (.inr s))) (finSumFinEquiv.symm p)
  | .inr q => Sum.elim (fun s => Sum.elim (fun i => C i (.inr s)) (0 : β → ℂ))
      (fun r => Sum.elim (0 : β → ℂ) (fun i => C i (.inl r))) (finSumFinEquiv.symm q)

def dblM {β : Type} {R S : ℕ} (C : Matrix β (Ix R S) ℂ) : Matrix (β ⊕ β) (Ix (R + S) (S + R)) ℂ :=
  Matrix.of fun i j => dblCol C j i

end GlobalTheory.RealLift.Dbl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairsRatioLocallyRationalTimesNormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definitePairs_ratio_locally_rational_times_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ (P₁ : GlobalTheory.LKDef.DPair G) (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
    Function.Injective ι → (∀ z : G.C, z * P₁.γ = P₁.γ * z ↔ ∃ w, ι w = z) →
    (∀ x, ι (c x) = P₁.β * sh G (ι x) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ), ∀ (P : GlobalTheory.LKDef.DPair G), P.γ = P₁.γ → P.c = P₁.c →
      (∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω) →
      ∀ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) → ∀ v ∉ S,
        ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y) := by
  first | (exact @GlobalTheory.LocTriv.ratio_local_norm_dpair) | (exact GlobalTheory.LocTriv.ratio_local_norm_dpair) | (intros; apply GlobalTheory.LocTriv.ratio_local_norm_dpair  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SkewDet

theorem det_ne_zero_of_isSkew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → W.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B n r s W hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := hW.sig w
  subst hrs
  intro hdet
  set φ : E →+* ℂ := (B.emb w).1
  set M : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := Complex.I • W.J.map φ with hM
  have hMdet : M.det = 0 := by
    rw [hM, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero, mul_zero]
  set P : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have hP : Pᵀ * M * P.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]
    ext i j
    simp [P, Matrix.mul_apply]
  have h2 := congrArg Matrix.det hP
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, hMdet, mul_zero, zero_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg] at h2
  rw [Matrix.det_one, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

end GlobalTheory.SkewDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHaarMatrixSpace
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem haar_exists_matrix_local_field : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ},
    ∃ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν := by
  intro k _ _ _ _ a d
  letI : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin d) k) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin d → k))
  exact ⟨Measure.addHaar, inferInstance⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactClopenNhdsOneGLFiniteAdelesStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_clopen_nhds_one_GL_finiteAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))), B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := by
  first | exact @GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | exact GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | (intros; apply GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen <;> assumption)
end

