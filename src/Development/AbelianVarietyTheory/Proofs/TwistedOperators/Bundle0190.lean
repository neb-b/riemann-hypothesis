module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdjoinRootLinearEquivOfCharpolyEq
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll

theorem exists_linearEquiv_mulVec_of_charpoly (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (P : PPol σ n) (A : Matrix (Fin n) (Fin n) E) (hA : A.charpoly = P.1) :
    ∃ φ : Fld P ≃ₗ[E] (Fin n → E), ∀ y, A *ᵥ φ y = φ (alpha P * y) := by

  let ψ : Fld P →ₐ[E] Matrix (Fin n) (Fin n) E :=
    Ideal.Quotient.liftₐ (Ideal.span {P.1}) (Polynomial.aeval A) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, ← hA, Matrix.aeval_self_charpoly, mul_zero])
  have hψα : ψ (alpha P) = A := by
    change Polynomial.aeval A Polynomial.X = A
    exact Polynomial.aeval_X A

  have hdim : Module.finrank E (Fld P) = n := by
    have h1 := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finrank
    rw [AdjoinRoot.powerBasis_dim] at h1
    exact h1.trans P.2.2.2.1
  have hpos : 0 < n := hdim ▸ Module.finrank_pos
  haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → E)
  let f : Fld P →ₗ[E] (Fin n → E) :=
    { toFun := fun y => ψ y *ᵥ v
      map_add' := fun y z => by simp [Matrix.add_mulVec]
      map_smul' := fun c y => by simp [Matrix.smul_mulVec] }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hne
    apply hv
    have h1 : ψ y⁻¹ * ψ y = 1 := by rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    have h2 : ψ y *ᵥ v = 0 := hy
    calc v = (ψ y⁻¹ * ψ y) *ᵥ v := by rw [h1, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  refine ⟨LinearMap.linearEquivOfInjective f hinj (by rw [hdim, Module.finrank_fin_fun]), fun y => ?_⟩
  simp only [LinearMap.linearEquivOfInjective_apply]
  change A *ᵥ (ψ y *ᵥ v) = ψ (alpha P * y) *ᵥ v
  rw [map_mul, hψα, Matrix.mulVec_mulVec]

end GlobalTheory.TrEll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.RealChar

variable {D : D7} {S T : HSp D}

theorem realPt_zero (C : Ctx S T) : C.realPt 0 = 0 := by
  funext σ k a
  simp [Ctx.realPt, compAt]

theorem th_zero_eq (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) : C.Th x φ 0 = thR C.X C.bas C.idx φ x 0 := by
  have h0 : IsRealPt (0 : WO S T) := by
    ext i j
    simp
  rw [(GlobalTheory.Ker.ZakEx.isZak_Th D S T C x hx φ hφ).1.2 0 h0, realPt_zero]

theorem th_zero_eq_thP (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) : C.Th x φ 0 = thP C.X C.hr C.bas C.idx φ 1 x := by
  have h := (GlobalTheory.SW.one_mem_rowHighest_and_thP_smul_one D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank).2 1 φ x
  rw [one_smul, one_mul] at h
  rw [h, th_zero_eq C hx hφ, thR]
  have hz : zR C.X C.idx x (0 : WR C.X S.rank) = 0 := by
    funext k i
    simp [zR, hermC]
  rw [hz, GlobalTheory.Ker.RealScalar.gaussR_zero C x, one_mul, thA]
  simp
  exact Or.inl rfl

theorem continuous_th_mvB (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (φ : TF S.rank C.g) (hφ : SW.IsSB φ) :
    Continuous (fun a : GA D T => C.Th (C.xB (C.mvB a B)) φ 0) := by
  have hS := fun B (hB : C.IsB B) => (GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  have hdom : ∀ a : GA D T, C.xB (C.mvB a B) ∈ C.X.dom := fun a => (hS _ ((hS B hB).2.2.2.2.2 a).1).2.1
  have e : (fun a : GA D T => C.Th (C.xB (C.mvB a B)) φ 0) =
      (thP C.X C.hr C.bas C.idx φ 1) ∘ fun a => C.xB (C.mvB a B) := by
    funext a
    exact th_zero_eq_thP C (hdom a) hφ
  rw [e]
  have hP := (GlobalTheory.SW.theta_holomorphic_weight D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (fun _ _ => 0)
    (fun _ _ => 0) φ hφ 1 (GlobalTheory.SW.one_mem_rowHighest_and_thP_smul_one D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank).1).1
  refine hP.continuousOn.comp_continuous ?_ hdom
  have hc : ∀ τ, Continuous fun a : GA D T => compAt C.θ τ (Formalism.L2.Theta.mt T a) := fun τ =>
    (GlobalTheory.RealWeil.continuous_compAt C.inf τ T.rank T.rank).comp (GlobalTheory.RealWeil.continuous_mt T).1
  refine continuous_pi fun σ => continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Ctx.xB, Ctx.mvB]
  exact Complex.continuous_conj.comp
    ((continuous_apply j).comp ((continuous_apply i).comp ((hc _).matrix_mul continuous_const)))

theorem exists_th_zero_ne (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (φ : TF S.rank C.g) (hφ : SW.IsSB φ)
    (h0 : φ ≠ 0) : ∃ φ' : TF S.rank C.g, SW.IsSB φ' ∧ C.Th (C.xB B) φ' 0 ≠ 0 := by
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  have R := GlobalTheory.Ker.thR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx φ hφ
  have hd := (GlobalTheory.Ker.zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx).2.2.2.1
  obtain ⟨y, hy⟩ : ∃ y, thR C.X C.bas C.idx φ (C.xB B) (embR C.X y) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hs : SW.IsSB ((0 : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 0
    have e : thR C.X C.bas C.idx φ (C.xB B) = thR C.X C.bas C.idx ((0 : ℂ) • φ) (C.xB B) := by
      rw [R.2.2.2.2 0, zero_smul]
      exact hd.equalizer R.1.continuous continuous_const (funext hn)
    exact h0 (((R.2.2.2.1 _ hs).1 e).trans (zero_smul ℂ φ))
  have hs' := ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y φ hφ).1
  refine ⟨_, hs', ?_⟩
  rw [th_zero_eq C hx hs', R.2.1 y 0, zero_add]
  exact mul_ne_zero (Complex.exp_ne_zero _) hy

end GlobalTheory.AdSpan.RealChar

namespace GlobalTheory.AdSpan.RealChar

theorem smul_cancel {α : Type} {F : α → ℂ} (hF : F ≠ 0) {c c' : ℂ} (h : c • F = c' • F) : c = c' := by
  obtain ⟨w, hw⟩ : ∃ w, F w ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hF (funext h')
  have := congrFun h w
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hw this

variable {D : D7} {S T : HSp D}

theorem th_ne (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  have L := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have hs : SW.IsSB ((0 : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 0
  have e : C.Th x φ = C.Th x ((0 : ℂ) • φ) := by rw [L.2.1, h, smul_zero]
  exact h0 (((L.1 _ hs).2 e).trans (zero_smul ℂ φ))

theorem th_zero (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) (h0 : φ = 0) : C.Th x φ = 0 := by
  have L := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have e : φ = (0 : ℂ) • φ := by rw [h0, smul_zero]
  rw [e, L.2.1, zero_smul]

theorem kZero_ne (C : Ctx S T) {x₁ x₂ : Frame C.X.Ψ T.rank} (h₁ : x₁ ∈ C.X.dom) (h₂ : x₂ ∈ C.X.dom) :
    kZero C.X C.idx x₁ x₂ (0 : Fin S.rank → Fin C.g → ℂ) 0 ≠ 0 := by
  rw [GlobalTheory.AdTh.Overlap.kZero_zero]
  exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
    (DblPoint.det_aLin_ne_zero h₁ h₂ τ) (DblPoint.det_aAnti_ne_zero h₁ h₂ τ)))

theorem realScal_character : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ContT C.ψ om → ∃ z : GA D T → ℂ, (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, z (a * a') = z a * z a') ∧ (∀ a ∈ GinfC T, ‖z a‖ = 1) ∧ ContinuousOn z (GinfC T : Set (GA D T)) ∧ ∀ B, C.IsB B → ∀ a ∈ GinfC T, RealScal C om B a (z a) := by
  intro D S T C om hom hcont
  obtain ⟨B₀, hB₀⟩ := (GlobalTheory.Ker.onBasis_frame_period D S T C).1
  have hS := fun B (hB : C.IsB B) => (GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  have hdom : ∀ B, C.IsB B → C.xB B ∈ C.X.dom := fun B hB => (hS B hB).2.1
  have hmvB : ∀ B, C.IsB B → ∀ g : GA D T, C.IsB (C.mvB g B) := fun B hB g => ((hS B hB).2.2.2.2.2 g).1
  have hex : ∀ B, C.IsB B → ∀ a ∈ GinfC T, ∃ c : ℂ, ‖c‖ = 1 ∧ RealScal C om B a c := fun B hB a ha =>
    GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom 1 (one_mem _) a ha B hB
  by_cases hne : ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ φ ≠ 0
  swap
  · refine ⟨fun _ => 1, fun _ _ _ _ => (mul_one 1).symm, fun _ _ => norm_one, continuousOn_const,
      fun B hB a ha φ hφ => ?_⟩
    obtain ⟨c, -, hc⟩ := hex B hB a ha
    have h0 : φ = 0 := by
      by_contra h
      exact hne ⟨φ, hφ, h⟩
    rw [hc φ hφ, th_zero C (hdom _ (hmvB B hB a)) hφ h0, smul_zero, smul_zero]
  obtain ⟨φ₀, hφ₀, h0⟩ := hne
  let z : GA D T → ℂ := fun a => if h : a ∈ GinfC T then (hex B₀ hB₀ a h).choose else 1
  have hz : ∀ a (ha : a ∈ GinfC T), ‖z a‖ = 1 ∧ RealScal C om B₀ a (z a) := fun a ha => by
    simp only [z, dif_pos ha]
    exact (hex B₀ hB₀ a ha).choose_spec
  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D S T C
  have hth : ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th (C.xB B) φ) :=
    fun B hB φ hφ => (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom B hB) φ hφ).1.1

  have hip2 : ∀ B B', C.IsB B → C.IsB B' → ∀ g : GA D T,
      ipO μ 𝓕 (C.Th (C.xB (C.mvB g B)) φ₀) (C.Th (C.xB (C.mvB g B')) φ₀) =
        ipO μ 𝓕 (C.Th (C.xB B) φ₀) (C.Th (C.xB B') φ₀) := fun B B' hB hB' g => by
    rw [GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ (hmvB B hB g)) (hdom _ (hmvB B' hB' g)) hφ₀ hφ₀,
      GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ hB) (hdom _ hB') hφ₀ hφ₀, GlobalTheory.AdTh.Overlap.kZero_mvB C hB g]
  have hdbl : dbl C.X C.bas C.idx φ₀ φ₀ 0 ≠ 0 := by
    intro hc
    have h1 := GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ hB₀) (hdom _ hB₀) hφ₀ hφ₀
    rw [hc, zero_mul] at h1
    exact th_ne C (hdom _ hB₀) hφ₀ h0 ((hip μ 𝓕 hμ _ (hth B₀ hB₀ φ₀ hφ₀)).2.1 h1)
  have hipne : ∀ B B', C.IsB B → C.IsB B' →
      ipO μ 𝓕 (C.Th (C.xB B) φ₀) (C.Th (C.xB B') φ₀) ≠ 0 := fun B B' hB hB' => by
    rw [GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ hB) (hdom _ hB') hφ₀ hφ₀]
    exact mul_ne_zero hdbl (kZero_ne C (hdom _ hB) (hdom _ hB'))

  have hind : ∀ B, C.IsB B → ∀ a (ha : a ∈ GinfC T), RealScal C om B a (z a) := by
    intro B hB a ha
    obtain ⟨c, -, hc⟩ := hex B hB a ha
    obtain ⟨hzn, hzs⟩ := hz a ha
    suffices e : c = z a by rw [← e]; exact hc
    have t1 := hth B hB φ₀ hφ₀
    have t2 := hth B₀ hB₀ φ₀ hφ₀
    have t1' := hth _ (hmvB B hB a) φ₀ hφ₀
    have t2' := hth _ (hmvB B₀ hB₀ a) φ₀ hφ₀
    have u := ((hip μ 𝓕 hμ _ t1).2.2.2 _ t2).2.2.2.2.2 om hom (1, a)
    have t3 : C.IsTh ((z a) • C.Th (C.xB (C.mvB a B₀)) φ₀) := hzs φ₀ hφ₀ ▸ hom.om_pres (1, a) _ t2
    rw [hc φ₀ hφ₀, hzs φ₀ hφ₀, ((hip μ 𝓕 hμ _ t1').2.2.2 _ t3).2.2.1,
      ((hip μ 𝓕 hμ _ t3).2.2.2 _ t1').2.1, ((hip μ 𝓕 hμ _ t2').2.2.2 _ t1').2.2.1, map_mul,
      ((hip μ 𝓕 hμ _ t1').2.2.2 _ t2').2.1, Complex.conj_conj, hip2 B B₀ hB hB₀ a] at u
    have K := hipne B B₀ hB hB₀
    have h1 : c * conj (z a) = 1 := mul_right_cancel₀ K (by linear_combination u)
    have h2 : z a * conj (z a) = 1 := by
      rw [Complex.mul_conj', hzn]; simp
    calc c = c * (z a * conj (z a)) := by rw [h2, mul_one]
      _ = (c * conj (z a)) * z a := by ring
      _ = z a := by rw [h1, one_mul]
  refine ⟨z, fun a ha a' ha' => ?_, fun a ha => (hz a ha).1, ?_, hind⟩
  ·
    have e1 := hind B₀ hB₀ (a * a') (mul_mem ha ha') φ₀ hφ₀
    have e2 := hind B₀ hB₀ a' ha' φ₀ hφ₀
    have e3 := hind _ (hmvB B₀ hB₀ a') a ha φ₀ hφ₀
    have hm : om (1, a * a') = om (1, a) * om (1, a') := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [hm, Module.End.mul_apply, e2, map_smul, e3, smul_smul,
      ← ((hS B₀ hB₀).2.2.2.2.2 a').2.1 a] at e1
    have := smul_cancel (th_ne C (hdom _ (hmvB B₀ hB₀ (a * a'))) hφ₀ h0) e1
    rw [← this, mul_comm]
  ·
    intro a₀ ha₀
    obtain ⟨φ, hφ, hφ0⟩ := exists_th_zero_ne C _ (hmvB B₀ hB₀ a₀) φ₀ hφ₀ h0
    have hN : Continuous fun a : GA D T => om (1, a) (C.Th (C.xB B₀) φ) 0 :=
      hcont _ (hth B₀ hB₀ φ hφ) 0
    have hD := continuous_th_mvB C B₀ hB₀ φ hφ
    have heq : ∀ a ∈ GinfC T, C.Th (C.xB (C.mvB a B₀)) φ 0 ≠ 0 →
        om (1, a) (C.Th (C.xB B₀) φ) 0 / C.Th (C.xB (C.mvB a B₀)) φ 0 = z a := fun a ha hne => by
      rw [hind B₀ hB₀ a ha φ hφ, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hne, mul_one]
    refine ContinuousWithinAt.congr_of_eventuallyEq
      ((hN.continuousAt.div hD.continuousAt hφ0).continuousWithinAt) ?_ (heq a₀ ha₀ hφ0).symm
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hD.continuousAt.eventually_ne hφ0)] with a ha hne
    exact (heq a ha hne).symm

end GlobalTheory.AdSpan.RealChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoverKFinitePairingOfRealIntertwiner
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine.CoverFromLocal

section General

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private theorem hasDerivAt_exp_smul_of_smoothVec {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H}
    (hw : SmoothVec Lie σ w) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) (dRep σ X w) 0 := by
  have h1 := hw 1 (fun _ => X) (fun _ => hX)
  have hc : ContDiff ℝ 1 (fun t : ℝ => (fun _ : Fin 1 => t)) := contDiff_pi.2 (fun _ => contDiff_id)
  have h2 := (h1.of_le (by first | simp | exact_mod_cast le_top)).comp hc
  have h3 := ((h2.differentiable one_ne_zero) 0).hasDerivAt
  have e : ((fun t : Fin 1 → ℝ => σ (List.ofFn fun i => NormedSpace.exp (t i • X)).prod w) ∘
      fun t : ℝ => (fun _ : Fin 1 => t)) = fun t : ℝ => σ (NormedSpace.exp (t • X)) w := by
    funext t
    simp [List.ofFn_succ]
  rw [e] at h3
  exact h3

private theorem barMat_map_conj_eq_reindex {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) :
    (barMat e Z).map (starRingEnd ℂ) = Matrix.reindex e e Z := by
  ext i j
  simp [barMat]

private theorem trace_map_conj' {p q : ℕ} (Z : Mat p q) :
    (Z.map (starRingEnd ℂ)).trace = (starRingEnd ℂ) Z.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.trace, Matrix.trace, map_sum]
  rfl

private theorem norm_apply_sub_I_smul_apply (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) :
    ‖U y - Complex.I • U x‖ = ‖x - Complex.I • y‖ := by
  have hU : U y - Complex.I • U x = U (y + Complex.I • x) := by
    rw [map_add (f := _), LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, neg_smul, sub_eq_add_neg]
  have hv : x - Complex.I • y = (-Complex.I) • (y + Complex.I • x) := by
    rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  rw [hU, U.norm_map, hv, norm_smul, norm_neg, Complex.norm_I, one_mul]

private theorem norm_apply_add_I_smul_apply (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) :
    ‖U y + Complex.I • U x‖ = ‖x + Complex.I • y‖ := by
  have hU : U y + Complex.I • U x = U (y - Complex.I • x) := by
    rw [map_sub, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, neg_smul, sub_neg_eq_add]
  have hv : x + Complex.I • y = Complex.I • (y - Complex.I • x) := by
    rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]
    abel
  rw [hU, U.norm_map, hv, norm_smul, Complex.norm_I, one_mul]

theorem inner_conjIso (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) : ⟪U y, U x⟫_ℂ = ⟪x, y⟫_ℂ := by
  have h1 : ‖U y + U x‖ = ‖x + y‖ := by rw [← map_add (f := _), U.norm_map, add_comm]
  have h2 : ‖U y - U x‖ = ‖x - y‖ := by rw [← map_sub, U.norm_map, norm_sub_rev]
  rw [inner_eq_sum_norm_sq_div_four (U y) (U x), inner_eq_sum_norm_sq_div_four x y]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, norm_apply_sub_I_smul_apply, norm_apply_add_I_smul_apply]

end General

theorem exists_coverW : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s) (A : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), (m : ℚ) = 2 * aT → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₁ M τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat e) m U → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₂ M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → IsPolyIso (M.ε τ) (M'.ε τ) e e' κ → LocW M M' τ aS aT A → ∃ B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V, CoverW R₁ R₂ B ∧ ∀ (P : LPol W.rank V.rank) (x : R₂.HK.V) (y : M'.sm τ), U' (y : M'.H τ) = R₂.ι x → R₁.ι (B (κ P) x) = U (A P y) := by
  intro D V W S S' M M' τ p q r s T₁ T₂ R₁ R₂ e e' m m' aS aT U U' κ A hm hm' h₁ h₂ hκ hA
  have hinj₁ : Function.Injective R₁.ι := R₁.ι_inj

  have hsm : ∀ x : R₂.HK.V, U'.symm (R₂.ι x) ∈ M'.sm τ := fun x =>
    Submodule.subset_span (h₂.smooth _ (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact Set.mem_range_self _))
  let w : R₂.HK.V → M'.sm τ := fun x => ⟨U'.symm (R₂.ι x), hsm x⟩
  have hUw : ∀ x, U' (w x : M'.H τ) = R₂.ι x := fun x => U'.apply_symm_apply _
  have hw_add : ∀ x x', w (x + x') = w x + w x' := by
    intro x x'
    apply Subtype.ext
    show U'.symm (R₂.ι (x + x')) = U'.symm (R₂.ι x) + U'.symm (R₂.ι x')
    rw [map_add (f := _), map_add (f := _)]
  have hw_smul : ∀ (c : ℂ) x, w (c • x) = (starRingEnd ℂ) c • w x := by
    intro c x
    apply Subtype.ext
    show U'.symm (R₂.ι (c • x)) = (starRingEnd ℂ) c • U'.symm (R₂.ι x)
    rw [map_smul, LinearIsometryEquiv.map_smulₛₗ]

  have hex : ∀ (P : LPol W.rank V.rank) (y : M'.sm τ), ∃ v, R₁.ι v = U (A P y) :=
    fun P y => (h₁.kfin _).1 (hA.kS P y)
  choose g hg using hex
  let Bf : Pol p q r s → R₂.HK.V → R₁.HK.V := fun P x => g (κ.symm P) (w x)
  have key : ∀ P x, R₁.ι (Bf P x) = U (A (κ.symm P) (w x)) := fun P x => hg _ _
  let Bi : Pol p q r s → (R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V) := fun P =>
    { toFun := Bf P
      map_add' := by
        intro x x'
        apply hinj₁
        show R₁.ι (Bf P (x + x')) = R₁.ι (Bf P x + Bf P x')
        rw [map_add (f := _), key, key, key, hw_add, map_add (f := _), map_add (f := _)]
      map_smul' := by
        intro c x
        apply hinj₁
        show R₁.ι (Bf P (c • x)) = R₁.ι ((starRingEnd ℂ) c • Bf P x)
        rw [map_smul, key, key, hw_smul, map_smul, map_smul] }
  let B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V :=
    { toFun := Bi
      map_add' := by
        intro P P'
        ext x
        apply hinj₁
        show R₁.ι (Bf (P + P') x) = R₁.ι (Bf P x + Bf P' x)
        rw [map_add (f := _), key, key, key, map_add (f := _), map_add (f := _), LinearMap.add_apply, map_add (f := _)]
      map_smul' := by
        intro c P
        ext x
        apply hinj₁
        show R₁.ι (Bf (c • P) x) = R₁.ι (c • Bf P x)
        rw [map_smul, key, key, map_smul, map_smul, LinearMap.smul_apply, map_smul] }
  have hB : ∀ P x, R₁.ι (B P x) = U (A (κ.symm P) (w x)) := key
  refine ⟨B, { adj := ?_, src := ?_, tgt := ?_ }, ?_⟩
  ·
    intro P x
    obtain ⟨b0, hb0K, hb0⟩ := hA.kT (κ.symm P) (U.symm (R₁.ι x))
    obtain ⟨b, hb⟩ := (h₂.kfin b0).1 hb0K
    refine ⟨b, fun y => ?_⟩
    have e2 : R₁.ι x = U (U.symm (R₁.ι x)) := (U.apply_symm_apply _).symm
    rw [hB, hb, ← hUw y, inner_conjIso, ← hb0]
    conv_lhs => rw [e2]
    exact LinearIsometryEquiv.inner_map_map U _ _
  ·
    intro Z hZ P y
    apply hinj₁
    have hloc : κ.symm (fockAct1 p q r s Z P) =
        locS (M.ε τ) (M'.ε τ) (Matrix.reindex e e Z) (κ.symm P) := by
      rw [LinearEquiv.symm_apply_eq, hκ.1, LinearEquiv.apply_symm_apply]
    have hX : toFrame M τ (barMat e Z) ∈ lieAt V τ := by
      rw [← h₁.lie]; exact ⟨Z, hZ, rfl⟩
    have hsx : SmoothVec (lieAt V τ) (M.rep τ) (A (κ.symm P) (w y)) :=
      h₁.smooth _ ⟨_, hB P y⟩
    have hd1 := hasDerivAt_exp_smul_of_smoothVec hsx hX
    have hdr : dRep (M.rep τ) (toFrame M τ (barMat e Z)) (A (κ.symm P) (w y)) =
        A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * toFrame M τ (barMat e Z) * (M.fr τ)⁻¹).map (starRingEnd ℂ))
          (κ.symm P) - ((aT : ℂ) * (toFrame M τ (barMat e Z)).trace) • κ.symm P) (w y) := by
      apply ext_inner_left ℂ
      intro u
      have hd2 := hA.src _ hX (κ.symm P) (w y) u
      have hd3 := (hasDerivAt_const (0 : ℝ) u).inner ℂ hd1
      simp only [inner_zero_left, add_zero] at hd3
      exact hd3.unique hd2
    have htr : (toFrame M τ (barMat e Z)).trace = -Z.trace := by
      rw [trace_toFrame, barMat, trace_reindex', trace_map_conj', trace_conj hZ]
    rw [fr_toFrame, barMat_map_conj_eq_reindex, htr] at hdr
    have hder := h₁.der Z hZ (B P y) _ (hB P y).symm
    rw [hdr] at hder
    have hc : ((m : ℂ) / 2 * Z.trace) = (aT : ℂ) * Z.trace := by
      have h2 : (m : ℂ) = 2 * (aT : ℂ) := by exact_mod_cast hm
      rw [h2]; ring
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_add (f := _), hc, hB] at hder
    rw [hB, hloc]
    rw [mul_neg, neg_smul, sub_neg_eq_add] at hder
    exact add_right_cancel hder
  ·
    intro Z hZ P y
    apply hinj₁
    rw [map_add (f := _), map_zero, hB, hB]
    have hp : plainMat e' Z = Matrix.reindex e' e' Z := rfl
    have hloc : κ.symm (fockAct2 p q r s Z P) =
        locT (M.ε τ) (M'.ε τ) (plainMat e' Z) (κ.symm P) := by
      rw [hp, LinearEquiv.symm_apply_eq, hκ.2, LinearEquiv.apply_symm_apply]
    have hY : toFrame M' τ (plainMat e' Z) ∈ lieAt W τ := by
      rw [← h₂.lie]; exact ⟨Z, hZ, rfl⟩
    have hsw : SmoothVec (lieAt W τ) (M'.rep τ) (w y : M'.H τ) :=
      h₂.smooth _ (by rw [hUw]; exact Set.mem_range_self _)
    have hd := hasDerivAt_exp_smul_of_smoothVec hsw hY
    have hder := h₂.der Z hZ y (w y) (hUw y)
    have hsm' : dRep (M'.rep τ) (toFrame M' τ (plainMat e' Z)) (w y : M'.H τ) ∈ M'.sm τ :=
      Submodule.subset_span (h₂.smooth _ (by rw [hder]; exact Set.mem_range_self _))
    have ht := hA.tgt _ hY (κ.symm P) (w y) ⟨_, hsm'⟩ hd
    have htr : (toFrame M' τ (plainMat e' Z)).trace = Z.trace := by
      rw [trace_toFrame, plainMat, trace_reindex']
    rw [htr, fr_toFrame] at ht
    have hcs : ((m' : ℂ) / 2 * Z.trace) + (starRingEnd ℂ) ((aS : ℂ) * Z.trace) = 0 := by
      have h2 : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
      rw [map_mul, trace_conj hZ, map_ratCast, h2]; ring
    have hw2 : w (R₂.HK.act Z y) = ⟨_, hsm'⟩ + ((aS : ℂ) * Z.trace) • w y := by
      apply Subtype.ext
      apply U'.injective
      rw [Submodule.coe_add, Submodule.coe_smul, map_add (f := _), LinearIsometryEquiv.map_smulₛₗ, hder, hUw, hUw,
        map_add, map_smul, add_assoc, ← add_smul, hcs, zero_smul, add_zero]
    rw [hloc, hw2, map_add (f := _), map_smul, ← map_add (f := _), ← map_zero U]
    congr 1
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply] at ht
    rw [← ht]
    abel
  ·
    intro P x y hy
    have hwy : w x = y := by
      apply Subtype.ext
      show U'.symm (R₂.ι x) = (y : M'.H τ)
      rw [← hy, LinearIsometryEquiv.symm_apply_apply]
    rw [hB, LinearEquiv.symm_apply_apply, hwy]

end GlobalTheory.Chain.RealLine.CoverFromLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtDiagSumProdPairingStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hasDerivAt_diag_eq_sum_mul_pairings : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, DifferentiableAt ℝ (fun t => M t x y) 0) →
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
      HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.hasDerivAt_diag_sum_prod_pairing | exact GlobalTheory.hasDerivAt_diag_sum_prod_pairing | (intros; apply GlobalTheory.hasDerivAt_diag_sum_prod_pairing <;> assumption)
end

