module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ProdBd
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharSel
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.KeyFock
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.NormCentral
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem aE_dM_eq (z w : (A E)ˣ) : aE z * dM w⁻¹ = gl (mD w) * aE (z * w⁻¹) := by
  refine Units.ext ?_
  have e : (gl (mD w)).val = !![(w : A E), 0; 0, ((w⁻¹ : (A E)ˣ) : A E)] := rfl
  rw [Units.val_mul, Units.val_mul, e, aE_val, aE_val, dM_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_left_comm]

private theorem scal_eq {K : Type} [Field K] [NumberField K] (u : (A K)ˣ) :
    GroundTheory.Automorphic.Reduction.scalarUnits K 2 u = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  ext i j
  rw [GroundTheory.Automorphic.Reduction.scalarUnits_apply, GroundTheory.Automorphic.Reduction.coe_diagUnits]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]

private theorem norm_central (s : {r : ℝ // 0 < r}) :
    ∃ z : (A E)ˣ, GroundTheory.Automorphic.Reduction.centralSection E 2 s = Matrix.GeneralLinearGroup.scalar (Fin 2) z ∧
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z) = GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s := by
  have hd : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : {r : ℝ // 0 < r}, s₀ ^ Module.finrank ℚ E = s := by
    refine ⟨⟨s.1 ^ ((Module.finrank ℚ E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩, Subtype.ext ?_⟩
    rw [Positive.val_pow]
    exact Real.rpow_inv_natCast_pow s.2.le hd
  obtain ⟨y, hy⟩ : ∃ y : (A ℚ)ˣ, GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s₀ = Matrix.GeneralLinearGroup.scalar (Fin 2) y :=
    ⟨_, (rfl : _ = GroundTheory.Automorphic.Reduction.scalarUnits ℚ 2 _).trans (scal_eq _)⟩
  refine ⟨ideleEmbedding ℚ E y, ?_, ?_⟩
  · rw [← hs₀, ← UpperTheory.centralSection_baseChange ℚ E 2 s₀, hy]
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]
  · rw [ideleNorm_ideleEmbedding, map_pow, ← hy, ← map_pow, hs₀]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.toII :
    ToII := by
  intro E _ _ _ D W M N P hP π hπ ⟨f, hf, ph, hph, φ, hφ, hne⟩
  obtain ⟨Φ, hΦ⟩ := UpperTheory.ConvolutionTheory.R2.smooth ℚ E D W M π f hf ph hph
  have hm : Φ ∈ span W M π := Submodule.subset_span ⟨f, hf, ph, hph, hΦ⟩
  have hBd : Bd fun x => Φ.1 x * φ.1 x := (UpperTheory.ConvolutionTheory.RankTwoDescent.prodBd E D W M N P π Φ hm φ hφ).1
  obtain ⟨-, hcont, hgl, hrat⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.meanLaws E N _ hBd
  let β : (A E)ˣ → ℂ := fun t => mean N fun x => Φ.1 (x * aE t) * φ.1 (x * aE t)
  have hβc : Continuous β := hcont.comp continuous_aE
  have hβi : ∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t := fun e t => by
    obtain ⟨γ, hγ⟩ := exists_ratGL_aE (F := E) e
    have h := hrat γ (aE t)
    simp only [β]
    rw [aE_mul, ← hγ]
    exact h
  have hJ : (J1 D N fun x => lift W M f.1 ph x * φ.1 x) =
      UI fun z => β (z * (Units.map (D.bar : A E →* A E) z)⁻¹) := by
    rw [← hΦ]
    refine congrArg UI (funext fun z => ?_)
    have h := hgl (mD (Units.map (D.bar : A E →* A E) z)) (aE (z * (Units.map (D.bar : A E →* A E) z)⁻¹))
    simp only [β, sZ]
    rw [aE_dM_eq]
    exact h
  obtain ⟨χ, h1, h2, h3⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.charSel E D β hβc hβi (by rw [← hJ]; exact hne)
  obtain ⟨χ₀, hχ₀⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.charDown E D χ h1
  have hdet : ∀ (g : G1 ℚ) (n : (A ℚ)ˣ), chiDet 2 χ₀ (gl g * dM n) = χ₀.1 n := fun g n => by
    have e : chiDet 2 χ₀ (gl g * dM n) = χ₀.1 (Matrix.GeneralLinearGroup.det (gl g * dM n)) := rfl
    rw [e, map_mul, det_gl, det_dM, one_mul]
  have hcs : ∀ s, chiDet 2 χ₀ (GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s) = 1 := fun s => by
    obtain ⟨z, hz, hn⟩ := norm_central (E := E) s
    have hz1 : χ₀.1 (ideleNorm ℚ E z) = 1 := by rw [← hχ₀ z]; exact h2 z ⟨s, hz.symm⟩
    have e : chiDet 2 χ₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z)) =
        χ₀.1 (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z))) := rfl
    rw [← hn, e, det_scalar, map_pow, hz1, one_pow]
  have hlift : ∀ x, lift W M (TR.mulChi 2 χ₀ f).1 ph x = ((χ₀.1 (nu ℚ x) : ℂˣ) : ℂ) * lift W M f.1 ph x := fun x => by
    simp only [lift]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [TR.mulChi_apply, hdet]
    ring
  refine ⟨π.twist χ₀, ?_, TR.mulChi 2 χ₀ f, ⟨f, hf, rfl⟩, ph, hph, φ, hφ, ?_⟩
  · rintro _ ⟨f₁, hf₁, rfl⟩ s g
    change f₁.1 _ * _ = f₁.1 g * _
    rw [hπ f₁ hf₁ s g, map_mul, hcs, one_mul]
  · have e : (II N fun x => lift W M (TR.mulChi 2 χ₀ f).1 ph x * φ.1 x) =
        UI fun t => ((χ.1 t : ℂˣ) : ℂ) * β t := by
      refine congrArg UI (funext fun t => ?_)
      simp only [mean, β]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      simp only [hlift, nu_mul, nu_gl, nu_aE, one_mul, hχ₀ t, hΦ]
      ring
    rw [e]
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEigAlt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem mc_fix {G V H : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] (ι : H →* G)
    (hsm : ∀ f, ∀ᶠ h in 𝓝 (1 : H), ρ (ι h) f = f) {c : G → ℂ} (hc : c ∈ I.MC ρ)
    (hinv : ∀ g h, c (g * ι h) = c g) :
    c ∈ Submodule.span ℂ {c | ∃ (Λ : V →ₗ[ℂ] ℂ) (f : V), (∀ h, ρ (ι h) f = f) ∧ c = fun x => Λ (ρ x f)} := by
  obtain ⟨n, a, b, hab⟩ := Submodule.mem_span_set'.1 hc
  choose Λ f hb using fun i => (b i).2
  have hval : ∀ x, c x = ∑ i, a i * Λ i (ρ x (f i)) := by
    intro x
    rw [← hab]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i]
  let R : H →* Module.End ℂ (Fin n → V) :=
    { toFun := fun h => LinearMap.pi fun i => (ρ (ι h)).comp (LinearMap.proj i)
      map_one' := LinearMap.ext fun x => funext fun i => by simp
      map_mul' := fun p q => LinearMap.ext fun x => funext fun i => by simp }
  have hR : ∀ h (x : Fin n → V) i, R h x i = ρ (ι h) (x i) := fun _ _ _ => rfl
  obtain ⟨s, hs, hfix⟩ := UpperTheory.ConvolutionTheory.R2.H.avg H (Fin n → V) R f (by
    have : ∀ᶠ h in 𝓝 (1 : H), ∀ i, ρ (ι h) (f i) = f i := Filter.eventually_all.2 fun i => hsm (f i)
    filter_upwards [this] with h hh
    funext i
    exact hh i)
  let S : Fin n → V := ∑ k ∈ s, R k f
  have hS : ∀ i, S i = ∑ k ∈ s, ρ (ι k) (f i) := fun i => by
    simp only [S, Finset.sum_apply, hR]
  have hcard : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hs)
  have key : c = (s.card : ℂ)⁻¹ • ∑ i, a i • fun x => Λ i (ρ x (S i)) := by
    funext x
    have h1 : (s.card : ℂ) * c x = ∑ k ∈ s, c (x * ι k) := by
      simp only [hinv, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ k ∈ s, c (x * ι k) = ∑ i, a i * Λ i (ρ x (S i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hval, hS, map_sum, map_mul, Module.End.mul_apply, Finset.mul_sum]
      exact Finset.sum_comm
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [← h2, ← h1, inv_mul_cancel_left₀ hcard]
  rw [key]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Λ i, S i, fun h => ?_, rfl⟩))
  have := congrFun (hfix h) i
  exact this

private theorem tj_fin {K : Type} [Field K] [NumberField K] (w : P K) (n : ℕ) {ϖ : Kv w} (hϖ : Formalism.UG.IsUnifV K w ϖ) (j : ℕ) :
    (Function.support fun c : GL (Fin n) (Kv w) ⧸ GlobalTheory.LFun.KGL w (n := n) => Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out).Finite := by
  have := GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm K w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j)
    (1 : Representation ℂ (GL (Fin n) (Kv w)) ℂ) (1 : ℂ)
  simpa using this

private theorem tj_sum {K : Type} [Field K] [NumberField K] (w : P K) (n : ℕ) {ϖ : Kv w} (hϖ : Formalism.UG.IsUnifV K w ϖ) (j : ℕ)
    (W : GL (Fin n) (Kv w) → ℂ) (g : GL (Fin n) (Kv w)) :
    ∑ᶠ c : GL (Fin n) (Kv w) ⧸ GlobalTheory.LFun.KGL w (n := n), Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out * W (g * c.out) =
      ∑ c ∈ (tj_fin w n hϖ j).toFinset, Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out * W (g * c.out) := by
  refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
  simp only [Set.Finite.coe_toFinset, Function.mem_support] at hc ⊢
  exact left_ne_zero_of_mul hc

private theorem eig_span {K : Type} [Field K] [NumberField K] (w : P K) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Kv w)) V) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL w ρ B)
    {c : GL (Fin n) (Kv w) → ℂ}
    (hc : c ∈ Submodule.span ℂ {c | ∃ (Λ : V →ₗ[ℂ] ℂ) (f : V), (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ρ k f = f) ∧ c = fun x => Λ (ρ x f)}) :
    Eig w B c := by
  induction hc using Submodule.span_induction with
  | mem c h =>
    obtain ⟨Λ, f, hf, rfl⟩ := h
    refine ⟨hB.card, fun g k hk => ?_, fun ϖ hϖ j hj g => ?_⟩
    · rw [map_mul, Module.End.mul_apply, hf k hk]
    · by_cases h0 : f = 0
      · subst h0
        simp
      have he := (hB.2 f (GlobalTheory.LGrp.mem_fixed.2 hf) h0).2.2.2 ϖ hϖ j hj
      let L : V →+ ℂ := (Λ.comp (ρ g)).toAddMonoidHom
      have hs := L.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm K w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ f)
      refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans ((congrArg L he).trans ?_))
      · simp [L, map_mul]
      · simp [L]
  | zero => exact ⟨hB.card, by simp, by simp⟩
  | add a b _ _ ha hb =>
    refine ⟨hB.card, fun g k hk => ?_, fun ϖ hϖ j hj g => ?_⟩
    · simp only [Pi.add_apply, ha.inv g k hk, hb.inv g k hk]
    · have e1 := ha.eig ϖ hϖ j hj g
      have e2 := hb.eig ϖ hϖ j hj g
      rw [tj_sum w n hϖ j] at e1 e2 ⊢
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, e1, e2]
  | smul z a _ ha =>
    refine ⟨hB.card, fun g k hk => ?_, fun ϖ hϖ j hj g => ?_⟩
    · simp only [Pi.smul_apply, ha.inv g k hk]
    · have e1 := ha.eig ϖ hϖ j hj g
      rw [tj_sum w n hϖ j] at e1 ⊢
      simp only [Pi.smul_apply, smul_eq_mul]
      calc _ = z * ∑ c ∈ (tj_fin w n hϖ j).toFinset, Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out * a (g * c.out) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _
        _ = _ := by rw [e1, mul_left_comm]

private theorem kgl_map {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] {n : ℕ} {v : P K} {w : P M}
    (c : Kv v ≃+* Kv w) (hc : ∀ x, Valued.v (c x) = Valued.v x) (g : GL (Fin n) (Kv v)) :
    g ∈ GlobalTheory.LFun.KGL v (n := n) ↔ Matrix.GeneralLinearGroup.map c.toRingHom g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hO : ∀ x, c x ∈ Formalism.UG.Ov M w ↔ x ∈ Formalism.UG.Ov K v := fun x => by
    change Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [hc]
  have hGv : ∀ (g : GL (Fin n) (Kv v)) i j, (Matrix.GeneralLinearGroup.map c.toRingHom g).1 i j = c (g.1 i j) := fun _ _ _ => rfl
  simp only [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv, hGv, hO]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.splitEig :
    SplitEig := by
  intro E _ _ _ D W M N P π Φ hΦ v w hs B hB hFix g
  obtain ⟨hq, i, hc, hx, hv⟩ := hs
  obtain ⟨θ, hθ⟩ := UpperTheory.ConvolutionTheory.R2.I.splt ℚ E D v w i hc hx
  have hmc := UpperTheory.ConvolutionTheory.R2.I.key ℚ E D W M π v θ _ hθ Φ hΦ g
  let gm : GL (Fin 2) (Kv v) →* GL (Fin 2) (Kv w) := Matrix.GeneralLinearGroup.map i.toRingHom
  let gi : GL (Fin 2) (Kv w) →* GL (Fin 2) (Kv v) := Matrix.GeneralLinearGroup.map i.symm.toRingHom
  have hgm : ∀ y, gm (gi y) = y := fun y => by
    ext a b
    simp [gm, gi]
  have hgi : ∀ y, gi (gm y) = y := fun y => by
    ext a b
    simp [gm, gi]
  let c : GL (Fin 2) (Kv v) → ℂ := fun x => WE D Φ.1 (g * lc w (gm x))
  have hinv : ∀ x (k : GlobalTheory.LFun.KGL v (n := 2)), c (x * (GlobalTheory.LFun.KGL v (n := 2)).subtype k) = c x := by
    intro x k
    have hk : gm k.1 ∈ GlobalTheory.LFun.KGL w (n := 2) := (kgl_map i hv k.1).1 k.2
    change WE D Φ.1 (g * lc w (gm (x * k.1))) = WE D Φ.1 (g * lc w (gm x))
    unfold WE
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [map_mul, map_mul, ← mul_assoc g, ← mul_assoc _ _ (lc w (gm k.1)), hFix _ _ hk]
  haveI : CompactSpace (GlobalTheory.LFun.KGL v (n := 2)) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL v 2).2
  have hsm : ∀ f, ∀ᶠ h in 𝓝 (1 : GlobalTheory.LFun.KGL v (n := 2)), π.locRep v ((GlobalTheory.LFun.KGL v (n := 2)).subtype h) f = f := fun f =>
    (continuous_subtype_val.tendsto (1 : GlobalTheory.LFun.KGL v (n := 2))).eventually
      (((UpperTheory.ConvolutionTheory.R2.I.locSm ℚ π v).1 f).mem_nhds (by simp))
  have h1 := mc_fix (π.locRep v) (GlobalTheory.LFun.KGL v (n := 2)).subtype hsm hmc hinv
  let ρ' : Representation ℂ (GL (Fin 2) (Kv w)) π.V := (π.locRep v).comp gi
  have hq' : Formalism.UG.qV E w = Formalism.UG.qV ℚ v := by
    simpa [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV] using hq
  have hB' : GlobalTheory.LFun.HasSatGL w ρ' B :=
    GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hv hq' (LinearEquiv.refl ℂ _) (fun x f => by
      change π.locRep v (gi (gm x)) f = π.locRep v x f
      rw [hgi]) hB
  have e : (fun y => WE D Φ.1 (g * finGL E 2 (locGL E 2 w y))) = LinearMap.funLeft ℂ ℂ gi c := by
    funext y
    change _ = WE D Φ.1 (g * lc w (gm (gi y)))
    rw [hgm]
    rfl
  rw [e]
  refine eig_span w ρ' hB' ((Submodule.map_span_le _ _ _).2 ?_ (Submodule.mem_map_of_mem h1))
  rintro _ ⟨Λ, f, hf, rfl⟩
  refine Submodule.subset_span ⟨Λ, f, fun k hk => ?_, rfl⟩
  have : gi k ∈ GlobalTheory.LFun.KGL v (n := 2) := (kgl_map i hv (gi k)).2 (by rwa [hgm])
  exact hf ⟨gi k, this⟩
end

