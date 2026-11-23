module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0001
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0002
public import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeBasic
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Basic

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
  {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem mat_mul' {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mulVec {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {x y : Fin n → AE F E} (h : mat g *ᵥ x = y) :
    mat g⁻¹ *ᵥ y = x := by
  rw [← h, Matrix.mulVec_mulVec, ← mat_mul', inv_mul_cancel, mat_one', Matrix.one_mulVec]

theorem pair_pres (hp : IsPair B M χX χW om r s r' s') (x) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : om x Φ ∈ schA F _ :=
  (IsUWeilPair.isUSplitting hp.weil).pres x Φ hΦ

theorem pair_cont (hp : IsPair B M χX χW om r s r' s') {l} (hl : l ∈ (adeleClass F).adm (Fin n × Fin d)) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : Continuous fun x => l (om x Φ) :=
  (IsUWeilPair.isUSplitting hp.weil).cont l hl Φ hΦ

theorem pair_adm (hp : IsPair B M χX χW om r s r' s') (x) {l} (hl : l ∈ (adeleClass F).adm (Fin n × Fin d)) :
    l ∘ₗ om x ∈ (adeleClass F).adm (Fin n × Fin d) :=
  (IsUWeilPair.isUSplitting hp.weil).adm x l hl

theorem om_mul (om : Rep σ X W) (x y) (Φ) : om x (om y Φ) = om (x * y) Φ := by rw [map_mul]; rfl

theorem rho_om (hp : IsPair B M χX χW om r s r' s') (g h) (a : Fin n → AE F E) (b : Fin d → AE F E) (c : AE F E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    M.co.rho B.ψ (c • Matrix.vecMulVec a b) (om (g, h) Φ) =
      om (g, h) (M.co.rho B.ψ (c • Matrix.vecMulVec (mat g⁻¹ *ᵥ a) (mat h⁻¹ *ᵥ b)) Φ) := by
  rw [(IsUWeilPair.isUSplitting hp.weil).impl (g, h) _ Φ hΦ]
  congr 2
  change _ = mat g * _ * (mat h)ᵀ
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mat_mul', ← mat_mul', mul_inv_cancel, mul_inv_cancel, mat_one', mat_one',
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem rho_linear (M : Model σ X W) (ψ) (u) {ι : Type} (t : Finset ι) (c : ι → ℂ) (Φ : ι → Fn F n d) :
    M.co.rho ψ u (∑ i ∈ t, c i • Φ i) = ∑ i ∈ t, c i • M.co.rho ψ u (Φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ev_adm {κ : Type} [Fintype κ] (y : κ → AF F) : (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  classical
  refine ⟨g (fun i => (y i).2) • ((BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem thetaSum_smul' {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem kfin_dec (hp : IsPair B M χX χW om r s r' s') {K : Subgroup (UA σ X.J)} {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hK : KFinite om K Φ) (S : Submodule ℂ (Fn F n d)) (hS : ∀ k : K, om (k.1, 1) Φ ∈ S) :
    ∃ (m : ℕ) (Ψ : Fin m → Fn F n d) (c : Fin m → K → ℂ), (∀ i, Ψ i ∈ S) ∧ (∀ i, Continuous (c i)) ∧
      ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i := by
  set V := Submodule.span ℂ (Set.range fun k : K => om (k.1, 1) Φ)
  haveI : FiniteDimensional ℂ V := hK
  let b := Module.finBasis ℂ V
  have hc : Continuous fun k : K => (⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩ : V) := by
    refine Continuous.subtype_mk (continuous_pi fun y => ?_) _
    exact (pair_cont hp (ev_adm y) hΦ).comp (continuous_subtype_val.prodMk continuous_const)
  refine ⟨_, fun i => (b i).1, fun i k => b.repr ⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩ i,
    fun i => Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hS k) (b i).2,
    fun i => (b.coord i).continuous_of_finiteDimensional.comp hc, fun k => ?_⟩
  have := congrArg Subtype.val (b.sum_repr ⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩)
  rw [Submodule.coe_sum] at this
  exact this.symm

end Basic

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.Leaves
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lawα {n d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ χ' : Chr F E} {x y : ℝ} {T : UA σ W.J → ℂ}
    (_n : n = n) (h : HasLaw W₁ H' χ x T) (e1 : χ = χ') (e2 : x = y) : HasLaw W₁ H' χ' y T := by subst e1 e2; exact h

theorem splitEx_of (hB : GenBig) (hSm : GenSmall) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hZ : EvZero) (hU : UnipEx) (hL : Low) (hT : TriplePair) : SplitEx := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h d₁ W₁ H' i₀ i₁ hH'
  obtain ⟨hp, hp', hw⟩ := hT F E σ B a a' G X om om' h
  obtain ⟨h1, h2, hW₁⟩ := (hL F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ h.base hH').2 h.geo.hW
  have hlt := h.geo.lt
  have hev := h.geo.even
  have heB := h.geo.eBig
  have haB := h.geo.aBig
  obtain ⟨k, hk⟩ := hev
  have uniq : ∀ f fa fb, Split2 W₁ H' X f fa fb → ∃! x : (UA σ G.W.J → ℂ) × (UA σ G.W.J → ℂ), Split2 W₁ H' X f x.1 x.2 :=
    fun f fa fb hs => ⟨(fa, fb), hs, fun y hy => Prod.ext (split_uniq hU h hH' hy hs).1 (split_uniq hU h hH' hy hs).2⟩
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V W₁ _ _ _ _ h.geo.hV hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp.hX hp.hW hp.resX (res_low hp.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp d₁ G.V W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + a') d₁ G.V G.W W₁ H' i₀ i₁ (a - G.p) G.p _ _ G.M M₁
      (by omega) ⟨(a - a') / 2, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om om₁ (IsPair.cast hp rfl rfl (by omega) (by omega)) hp₁ Φ hΦ (by simp)
    exact uniq _ A₁ A₀ ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V' W₁ _ _ _ _ h.geo.hV' hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp'.hX hp'.hW hp'.resX (res_low hp'.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp' d₁ G.V' W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anySmall hSm hA hK hS hI hP hPl hC F E σ B a' (a + a') d₁ G.V' G.W W₁ H' i₀ i₁ G.q (a' - G.q) _ _ G.M' M₁
      (by omega) ⟨(a - a') / 2 + 1, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om' om₁ (IsPair.cast hp' rfl rfl (by omega) (by omega)) hp₁ Φ hΦ.1 (fun _ => hΦ.2)
    exact uniq _ A₀ A₁ ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩

theorem ctBigZero_of (hB : GenBig) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hU : UnipEx) (hT : TriplePair) : CTBigZero := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  obtain ⟨eV, ep, eq, hH, hH'⟩ := hc
  dsimp only at eV ep eq hH hH' he
  subst eV ep
  by_cases hex : ∃ X om om', IsTriple B G X om om'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' _ _ h => absurd ⟨X, om, om', h⟩ hex⟩
  obtain ⟨X0, o, o', h0⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨C₀, hC₀, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + (b + 2)) (a + b) G.V G.W W₁ H' _ _ (a - G.p) G.p
    (a + b - (G.p + q₁)) (G.p + q₁) G.M M₁ (by omega) ⟨(a - (b + 2)) / 2, by omega, by omega⟩ hH' e he
  refine ⟨C₀, hC₀, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₁ (IsPair.cast (hT F E σ B _ _ G X om om' h).1 rfl rfl (by omega) (by omega))
    (hT F E σ B _ _ _ X om₁ om₁' h₁).1 Φ hΦ (by simp)
  have := split_uniq hU h hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.2]
  exact c4 g m hm x (by simp)

theorem ctSmallZero_of (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hT : TriplePair) : CTSmallZero := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he
  obtain ⟨C, hC, H0⟩ := hA F E σ B a' _ _ G.V' G.W G₁.W H' _ _ G.q (a' - G.q) (b + 2 + a' - (G.p + G.q)) (G.p + G.q)
    (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) G₁.V' G.M' G₁.M' hc.eV (by rw [hc.q0]; simp) hc.hH' e he
  refine ⟨C, hC, fun X om om' om₁ om₁' h h₁ Φ hΦ => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  obtain ⟨K, μK, μ, hK1, -⟩ := hS F E σ B _ G.V' _ _ h.base hp.herm
  obtain ⟨A₀, c1, c2, c3⟩ := H0 _ _ om' om₁' hp
    (IsPair.cast (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1 (by rw [hc.q0, hc.q1]) (by rw [hc.q0, hc.q1]) rfl rfl) Φ
    (hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ).1
  exact ⟨A₀, ⟨by rwa [add_zero], c2, fun t m _ h => by simp⟩, c3⟩

theorem ctBigCone_of (hB : GenBig) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTBigCone := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.q0
  have e3 := hc.q1
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V G₁.W _ _ _ _ h0.geo.hV h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ o _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).1 _ G.V G₁.W H' _ _ M₁ rfl hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V G.W G₁.V G₁.W H H' _ _ _ _ (b - G₁.p) G₁.p (b + a' - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M G₁.M hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM he₀ he ((b + 2 - a') / 2) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V _ _ H h0.base h0.geo.hV (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨hs1, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₂ om₁ (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hs1 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.1, (c4 g m hm x).1, inv_div]
  rfl

theorem ctSmallCone_of (hB : GenSmall) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTSmallCone := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.eq
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V' G₁.W _ _ _ _ h0.geo.hV' h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ o' _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).2.1 _ G.V' G₁.W H' _ _ M₁ rfl
    hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V' G.W G₁.V' G₁.W H H' _ _ _ _ G₁.q (b - G₁.q) (a + b - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M' G₁.M' hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM' he₀ he ((a - (b + 2)) / 2 + 1) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V' _ _ H h0.base h0.geo.hV' (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨-, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ.1
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om' om₂ om₁' (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hΦ.2 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₀) (fb' := A₁) ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩
  rw [this.2, (c4 g m hm x).1]
  rfl

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.StabDec
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr

theorem stabDec_of : StabDec := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  obtain ⟨ε, A', h⟩ := isFr hB hY hH
  have e : fr (incM F H.ι) (incV F H.x) (incV F H.y) = incM F (fr H.ι H.x H.y) := fr_map _
  refine ⟨fun p t hp => ?_, fun ξ g₁ hg m hm => ?_, fun t g₁ m hm u hu => levi_conj hm hu⟩
  · obtain ⟨u, hu, g₁, m, h1, h2, h3⟩ := stab_dec hB.cm h (det_ne hY) p t hp
    refine ⟨u, hu, g₁, m, h1, h2, fun hr => ?_⟩
    obtain ⟨M, hM⟩ := mem_ratU.1 hr
    refine mem_ratU.2 ⟨(A' * M * fr H.ι H.x H.y).toBlocks₁₁, ?_⟩
    rw [h3, hM, e, incM, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  · obtain ⟨m', h1, h2⟩ := exists_levi hB.cm h (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) g₁
    obtain ⟨M, hM⟩ := mem_ratU.1 hg
    rw [levi_uniq h hm h1]
    refine mem_ratU.2 ⟨fr H.ι H.x H.y * dg M ξ.1 (σ (ξ⁻¹).1) * A', ?_⟩
    rw [h2, hM, e, incM, incM, incM, incM, Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext (i | i) (j | j)
    · rfl
    · exact (map_zero (inclR (F := F) (E := E) (AF F))).symm
    · exact (map_zero (inclR (F := F) (E := E) (AF F))).symm
    · fin_cases i <;> fin_cases j
      exacts [rfl, (map_zero (inclR (F := F) (E := E) (AF F))).symm, (map_zero (inclR (F := F) (E := E) (AF F))).symm, rfl]

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.UnfMod
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.Doubling (absE)

noncomputable section

namespace PositivityTheory.ThKCT.Unf

theorem lattice_one {V Λ : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddRightInvariant]
    (h0 : μ ≠ 0) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) {C : Set V} (hC : MeasurableSet C) (hf : μ C ≠ ⊤)
    (cov : ∀ y, ∃ l, y + j l ∈ C) (fin : ∀ y, {l | y + j l ∈ C}.Finite) (T : V →+ V) (hT : Measurable T) (t : Λ ≃ Λ)
    (ht : ∀ l, T (j l) = j (t l)) {c : ℝ≥0} (hc : μ.map T = c • μ) : c = 1 := by
  let S : V → ℝ≥0∞ := fun y => ∑' l, C.indicator 1 (y + j l)
  have hi : Measurable (C.indicator (1 : V → ℝ≥0∞)) := measurable_one.indicator hC
  have hS : Measurable S := Measurable.tsum fun l => hi.comp (measurable_add_const _)
  have S1 : ∀ y, 1 ≤ S y := fun y => by
    obtain ⟨l, hl⟩ := cov y
    exact le_trans (by simp [hl]) (ENNReal.le_tsum l)
  have S2 : ∀ y, S y ≠ ⊤ := fun y => by
    simp only [S]
    rw [tsum_eq_sum (s := (fin y).toFinset) fun l hl => Set.indicator_of_notMem (by simpa using hl) _]
    exact ENNReal.sum_ne_top.2 fun l _ => by by_cases h : y + j l ∈ C <;> simp [h]
  have S3 : ∀ y l, S (y + j l) = S y := fun y l => by
    simp only [S, add_assoc, ← map_add (f := _)]
    exact (Equiv.addLeft l).tsum_eq fun m => C.indicator 1 (y + j m)
  let β : V → ℝ≥0∞ := fun y => C.indicator 1 y * (S y)⁻¹
  have hβ : Measurable β := hi.mul hS.inv
  have b1 : ∀ y, ∑' l, β (y + j l) = 1 := fun y => by
    simp only [β, S3]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel (zero_lt_one.trans_le (S1 y)).ne' (S2 y)
  have b2 : ∀ y, ∑' l, β (T (y + j l)) = 1 := fun y => by
    simp only [map_add (f := _), ht]
    exact (t.tsum_eq fun l => β (T y + j l)).trans (b1 _)
  have half : ∀ f g : V → ℝ≥0∞, Measurable f → Measurable g → (∀ y, ∑' l, g (y + j l) = 1) →
      ∫⁻ y, f y ∂μ = ∑' l, ∫⁻ y, f y * g (y + j l) ∂μ := fun f g h1 h2 h3 => by
    rw [← lintegral_tsum (f := fun l y => f y * g (y + j l)) fun l => (h1.mul (h2.comp (measurable_add_const _))).aemeasurable]
    simp only [ENNReal.tsum_mul_left, h3, mul_one]
  have e : ∫⁻ y, β (T y) ∂μ = ∫⁻ y, β y ∂μ := by
    rw [half (fun y => β (T y)) β (hβ.comp hT) hβ b1, half β (fun y => β (T y)) hβ (hβ.comp hT) b2, ← (Equiv.neg Λ).tsum_eq]
    refine tsum_congr fun l => ?_
    rw [← lintegral_add_right_eq_self _ (j l)]
    simp [mul_comm]
  rw [← lintegral_map hβ hT, hc, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul] at e
  have n0 : ∫⁻ y, β y ∂μ ≠ 0 := fun h => h0 (by
    rw [← Measure.measure_univ_eq_zero, ← lintegral_one, half _ β measurable_const hβ b1]
    simp [lintegral_add_right_eq_self β, h])
  have n1 : ∫⁻ y, β y ∂μ ≠ ⊤ := ne_top_of_le_ne_top hf (by
    rw [← lintegral_indicator_one hC]
    exact lintegral_mono fun y => mul_le_of_le_one_right' (ENNReal.inv_le_one.2 (S1 y)))
  exact_mod_cast (ENNReal.mul_left_inj n0 n1).1 (e.trans (one_mul _).symm)

theorem eq_one_of_bdd {T : Type} [Group T] (φ : T →* ℝ≥0) {b : ℝ≥0} (h : ∀ t, φ t ≤ b) (t : T) : φ t = 1 := by
  have k : ∀ t, φ t ≤ 1 := fun t => not_lt.1 fun h1 => by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b h1
    exact absurd (h (t ^ n)) (by rw [map_pow]; exact not_le.2 hn)
  refine le_antisymm (k t) ?_
  calc 1 = φ t * φ t⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ φ t := mul_le_of_le_one_right' (k _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem absE_flow (h : IsCMExt F E σ) {τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ} (hτ : IsFlow τ) (x : ℝ) :
    (absE F E (τ (Multiplicative.ofAdd x)) : ℝ) = Real.exp (2 * Module.finrank ℚ F * x) := by
  obtain ⟨-, θ, hθ, hv⟩ := hτ
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have e := GlobalTheory.CompanionTheory.SW.FChi.norm_tmul_one h.2.2.1 (AF F) (pairA F (θ (Real.exp x)) 1)
  rw [← hv] at e
  simp only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf, e, map_pow]
  have e1 : ∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.AdelicU.evFin F v (pairA F (θ (Real.exp x)) 1) = 1 := fun v =>
    map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
  have e2 : ∀ w : InfinitePlace F, ‖GlobalTheory.AdelicU.evInf F w (pairA F (θ (Real.exp x)) 1)‖ = Real.exp x := fun w => by
    have := Complex.ringHom_eq_ofReal_of_continuous (f := (InfinitePlace.Completion.extensionEmbedding w).comp
      ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp θ))
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp hθ))
    have h2 := congrArg (fun f : ℝ →+* ℂ => ‖f (Real.exp x)‖) this
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
    refine Eq.trans h2 ?_
    simp
  simp only [e1, one_pow, nnnorm_one, finprod_one, mul_one, NNReal.coe_prod, NNReal.coe_pow, nnnorm_pow, coe_nnnorm, e2,
    Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  rw [← pow_mul, ← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem modulus (h : IsCMExt F E σ) (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F))
    (hW : μW.IsAddHaarMeasure) (hA : μA.IsAddHaarMeasure) : ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧
      (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p => (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1,
        Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) = χ a • μW.prod μA) ∧ ∀ a, χ a * absE F E a ^ (M + 1) = 1 := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ h (AF F)
  have := hB 1 M
  have : BorelSpace (AF F) := ⟨rfl⟩
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable F := Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.CompanionTheory.SW.Flow.exists_flow F E σ h
  obtain ⟨χ, χc, χ1, χ2⟩ := _root_.GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi F E σ h τ hτ M μW μA hW hA
  obtain ⟨ω, hω, hid⟩ := _root_.GlobalTheory.CompanionTheory.SW.Fujisaki.units_decomp F E σ h τ hτ
  obtain ⟨⟨CW, hCW, cW⟩, fW, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.CocW.main F E σ h 1 M
  obtain ⟨⟨CA, hCA, cA⟩, fA, -⟩ := _root_.GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact F
  have rt : ∀ X Y : Fin 1 → Fin M → E, ratTup (F := F) (AF F) (X + Y) = ratTup (AF F) X + ratTup (AF F) Y :=
    fun X Y => funext fun a => funext fun i => map_add _ _ _
  have rat : ∀ (l : Eˣ) (a : (AF F ⊗[F] E)ˣ), (a : AF F ⊗[F] E) = inclR (AF F) (l : E) → χ a = 1 := fun l a hl => by
    have hs : σ l ≠ 0 := (map_ne_zero σ).2 l.ne_zero
    have hn : Algebra.norm F (l : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 l.ne_zero
    let j : (Fin 1 → Fin M → E) × F →+ (Fin 1 → Fin M → AF F ⊗[F] E) × AF F :=
      (AddMonoidHom.mk' _ rt).prodMap (algebraMap F (AF F)).toAddMonoidHom
    refine lattice_one (μW.prod μA) (NeZero.ne _) j (hCW.prod hCA).measurableSet (hCW.prod hCA).measure_lt_top.ne
      (fun y => ?_) (fun y => ?_) ((DistribSMul.toAddMonoidHom _ (sigR (AF F) σ (a : AF F ⊗[F] E))).prodMap
        (AddMonoidHom.mulLeft (Algebra.norm (AF F) (a : AF F ⊗[F] E)))) ?_
      ((MulAction.toPerm (Units.mk0 _ hs)).prodCongr (Equiv.mulLeft₀ _ hn)) (fun l' => Prod.ext ?_ ?_) (χ1 a)
    · obtain ⟨X, hX⟩ := cW y.1
      obtain ⟨r, hr⟩ := cA y.2
      exact ⟨-(X, r), by rw [map_neg, ← sub_eq_add_neg]; exact ⟨hX, hr⟩⟩
    · refine ((fW _ (hCW.image (continuous_const_add (-y.1)))).prod (fA _ (hCA.image (continuous_const_add (-y.2))))).subset ?_
      exact fun l' hl' => ⟨⟨_, hl'.1, neg_add_cancel_left _ _⟩, ⟨_, hl'.2, neg_add_cancel_left _ _⟩⟩
    · exact ((continuous_const_smul _ : Continuous fun x : Fin 1 → Fin M → AF F ⊗[F] E => (_ : AF F ⊗[F] E) • x).prodMap (continuous_const.mul continuous_id : Continuous fun x : AF F => _ * x)).measurable
    · funext b i
      show sigR (AF F) σ (a : AF F ⊗[F] E) * inclR (AF F) (l'.1 b i) = inclR (AF F) (σ l * l'.1 b i)
      rw [hl, map_mul]; rfl
    · show Algebra.norm (AF F) (a : AF F ⊗[F] E) * algebraMap F (AF F) l'.2 = algebraMap F (AF F) (Algebra.norm F (l : E) * l'.2)
      rw [hl, map_mul]
      exact congrArg (· * _) (GlobalTheory.Doubling.norm_inclR _)
  have hc : Continuous fun a => χ a * absE F E a ^ (M + 1) := χc.mul (GlobalTheory.Doubling.continuous_absE.pow _)
  obtain ⟨b, hb⟩ := (hω.image hc).bddAbove
  refine ⟨χ, χc, χ1, eq_one_of_bdd (χ * (powMonoidHom (M + 1)).comp (absE F E)) (b := b) fun a => ?_⟩
  obtain ⟨l, a', x, j, hl, hx, rfl⟩ := hid a
  have e1 : absE F E a' = 1 := by
    rw [← GlobalTheory.Doubling.absE_inclR (F := F) l]
    exact congrArg _ (Units.ext hl)
  have e2 : χ (τ (Multiplicative.ofAdd (j : ℝ))) * absE F E (τ (Multiplicative.ofAdd (j : ℝ))) ^ (M + 1) = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_pow, χ2, absE_flow h hτ, ← Real.exp_nat_mul, ← Real.exp_add, NNReal.coe_one, Real.exp_eq_one_iff]
    push_cast
    ring
  rw [map_mul, map_mul]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, powMonoidHom_apply, rat l a' hl, e1, e2, one_pow, one_mul]
  exact hb ⟨x, hx, rfl⟩

end PositivityTheory.ThKCT.Unf
end
end

