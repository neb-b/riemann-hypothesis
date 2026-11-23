module

public import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.RealInvL
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.PolZero
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_left {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Φ : Fn F n d}
    (h : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) :
    ∀ γ ∈ ratU σ W.J, ∀ x, M.I om Φ (γ * x) = M.I om Φ x := fun γ hγ x => by
  unfold Model.I
  have e : ∀ g, theta om Φ g (γ * x) = theta om Φ g x := fun g => by simpa only [one_mul] using h 1 (one_mem _) γ hγ g x
  simp only [e]

theorem swap_bdd {A B : Type} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : A × B → ℂ} (c : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ∫ a, ∫ b, f (a, b) ∂ν ∂μ = ∫ b, ∫ a, f (a, b) ∂μ ∂ν :=
  integral_integral_swap (f := fun a b => f (a, b)) (Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC))

theorem int_th {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Ψ : Fn F n d}
    (cX : Cpt σ X.J) (cW : Cpt σ W.J) (h1 : M.μ.IsHaarMeasure) (h2 : IsFundamentalDomain (ratU σ X.J) M.dom M.μ)
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ)
    (hc : Continuous fun x : UA σ X.J × UA σ W.J => theta om Ψ x.1 x.2)
    (hi : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Ψ (γ * g) (γ' * h) = theta om Ψ g h)
    {φ : UA σ W.J → ℂ} (pc : Continuous φ) (pi : ∀ γ ∈ ratU σ W.J, ∀ g, φ (γ * g) = φ g) :
    ∫ g in M.dom, th om μ D φ Ψ g ∂M.μ = pet μ D φ (M.I om Ψ) := by
  haveI := cX.sc; haveI := cW.sc
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := isFiniteMeasure_restrict.2 (cX.fin _ _ h1 h2).ne
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have c : Continuous fun x : UA σ X.J × UA σ W.J => φ x.2 * star (theta om Ψ x.1 x.2) := (pc.comp continuous_snd).mul hc.star
  obtain ⟨C, hC⟩ := cX.bdd₂ cW c fun γ hγ δ hδ g g' => by simp only [pi δ hδ, hi γ hγ δ hδ]
  unfold th pet Model.I
  refine (swap_bdd _ _ c hC).trans <| integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [integral_const_mul]
  exact congrArg _ integral_conj

theorem polZero_of (hC : CptAll) (hH : HermLine) (hL : CoefLine) (hT : ThConst) (hN : NonZeroAn) (hM : MatchEx)
    (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : PolZero := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq
  have t := h.triple
  have cW := hC F E σ B _ G.W _ _ t.base (Or.inr t.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ t.base (Or.inl t.geo.hV') (by omega)
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  obtain ⟨m1, m2, m3⟩ := hM F E σ B a a' G X om om' R Rf h
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1
  have s1 : ∀ y ∈ pairs B G X R Rf, y.1 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) _ (m3 _ _ hy.1 hy.2).1
  have s2 : ∀ y ∈ pairs B G X R Rf, y.2 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) _ (m3 _ _ hy.1 hy.2).2.1
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1 (Or.inr (by omega))
  have cc : ∀ s u, ∀ y ∈ pairs B G X R Rf, Continuous (comb G om om' s u y) := fun s u y hy =>
    ((c1 _ (s1 y hy)).const_smul s).add ((c2 _ (s2 y hy)).const_smul u)
  have ci : ∀ s u, ∀ y ∈ pairs B G X R Rf, ∀ γ ∈ ratU σ G.W.J, ∀ g, comb G om om' s u y (γ * g) = comb G om om' s u y g :=
    fun s u y hy γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_left G.M (b1 _ (s1 y hy)).2.1 γ hγ, I_left G.M' (b2 _ (s2 y hy)).2.1 γ hγ]
  have e01 : ∀ y, comb G om om' 0 1 y = G.M'.I om' y.2 := fun y => by simp [comb]
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have ig : ∀ s u s' u', ∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf,
      Integrable (fun g => comb G om om' s u y g * star (comb G om om' s' u' y' g)) (μ.restrict D) := fun s u s' u' y hy y' hy' => by
    have c := (cc s u y hy).mul (cc s' u' y' hy').star
    obtain ⟨C, hC⟩ := cW.bdd c fun γ hγ g => by
      change comb G om om' s u y (γ * g) * star (comb G om om' s' u' y' (γ * g)) =
        comb G om om' s u y g * star (comb G om om' s' u' y' g)
      rw [ci s u y hy γ hγ, ci s' u' y' hy' γ hγ]
    exact Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC)
  obtain ⟨c, hc⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 0 0 1
  have orth : ∀ y ∈ pairs B G X R Rf, pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) = 0 := fun y hy => by
    have e : pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) =
        pet μ D (comb G om om' 1 0 y) (comb G om om' 0 1 y) - c * pet μ D (comb G om om' 0 1 y) (comb G om om' 0 1 y) := by
      unfold pet
      rw [← integral_const_mul, ← integral_sub (ig _ _ _ _ y hy y hy) ((ig _ _ _ _ y hy y hy).const_mul c)]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, hc y hy y hy, sub_self]
  obtain ⟨lam, hl⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) 1 (-c)
  obtain ⟨⟨Φ₀, q1, q2⟩, Φ', r1, r2⟩ := And.imp (fun f => f hp) (fun f => f hq) (hN F E σ B a a' G X om om' t)
  obtain ⟨Φ, hΦ⟩ := m2 Φ' r1.1
  have hy : (Φ, Φ') ∈ pairs B G X R Rf := ⟨r1.2, hΦ⟩
  have v0 := cV.vol_ne t.geo.hM'.haar t.geo.hM'.dom
  have key : ∀ s u, th om' μ D (comb G om om' s u (Φ, Φ')) Φ' =
      fun _ => pet μ D (comb G om om' s u (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) / (G.M'.μ.real G.M'.dom : ℂ) := fun s u => by
    have k := (hT F E σ B a a' G X om om' R Rf h s u (fun y hy => cW.rapid (cc s u y hy) (ci s u y hy)) μ D hμ hD _ hy).2 Φ'
      (s2 _ hy)
    have i := int_th G.M' cV cW t.geo.hM'.haar t.geo.hM'.dom hμ hD (b2 _ (s2 _ hy)).1 (b2 _ (s2 _ hy)).2.1 (cc s u _ hy) (ci s u _ hy)
    simp only [k, setIntegral_const, Complex.real_smul] at i
    funext g
    rw [k, e01, ← i, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 v0)]
  have n0 : pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) ≠ 0 := fun h0 =>
    r2 (e01 (Φ, Φ') ▸ cW.eq_zero hμ hD (cc 0 1 _ hy) (ci 0 1 _ hy) h0)
  have l0 : lam = 0 := by
    have := hL F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) lam hl _ hy Φ' r1.1
    rw [key, key, orth _ hy] at this
    generalize pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) = x at this n0
    simpa [pet, n0, v0] using this
  have main : PolConst B G X om om' R Rf c := fun Ψ Ψ' h1 h2 g => by
    have hz : (Ψ, Ψ') ∈ pairs B G X R Rf := ⟨h1, h2⟩
    have := congrFun (cW.eq_zero hμ hD (cc 1 (-c) _ hz) (ci 1 (-c) _ hz) (by rw [hl _ hz _ hz, l0, zero_mul])) g
    simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linear_combination this
  refine ⟨c, fun c0 => q2 (funext fun g => ?_), main⟩
  obtain ⟨Ψ', h1, h2⟩ := m1 Φ₀ q1
  rw [main Φ₀ Ψ' h1 h2 g, c0, zero_mul]; rfl

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.RealInv
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal ENNReal Matrix Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace Dense

theorem exists_fixed {S H P : Type} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [AddCommGroup P] [Module ℂ P] (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι) (p : S →ₗ[ℂ] P) (N : Submodule ℂ S)
    [FiniteDimensional ℂ N] {f : S} (hf : f ∈ N) (hp : p f ≠ 0) :
    ∃ f₀ ∈ N, f₀ ≠ 0 ∧ ∀ g ∈ N, p g = p f₀ → ‖ι g‖ = ‖ι f₀‖ → g = f₀ := by
  let Z := (N ⊓ LinearMap.ker p).map ι
  haveI : FiniteDimensional ℂ (N ⊓ LinearMap.ker p : Submodule ℂ S) := Submodule.finiteDimensional_of_le inf_le_left
  haveI : CompleteSpace Z := FiniteDimensional.complete ℂ Z
  obtain ⟨_, ⟨z, hz, rfl⟩, y, hy, e⟩ := Z.exists_add_mem_mem_orthogonal (ι f)
  have e' : ι (f - z) = y := by rw [map_sub, e, add_sub_cancel_left]
  refine ⟨f - z, sub_mem hf hz.1, fun h => hp ?_, fun g hg h1 h2 => ?_⟩
  · rw [sub_eq_zero.1 h]
    exact hz.2
  · have hm : ι (g - (f - z)) ∈ Z := ⟨_, ⟨sub_mem hg (sub_mem hf hz.1), by simp [h1]⟩, rfl⟩
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (hy _ hm)
    rw [← e', ← map_add (f := _), sub_add_cancel, h2, right_eq_add, mul_self_eq_zero, norm_eq_zero] at this
    exact sub_eq_zero.1 (hι (this.trans (map_zero ι).symm))

def dopL {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) where
  toFun := dop a L
  map_add' f g := by
    ext x
    simp only [dop_apply, SchwartzMap.add_apply]
    rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, fderiv_add f.differentiableAt g.differentiableAt, ContinuousLinearMap.add_apply]
    ring
  map_smul' c f := by
    ext x
    simp only [dop_apply, SchwartzMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [show ⇑(c • f) = c • ⇑f from rfl, fderiv_const_smul f.differentiableAt, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

theorem exists_dop_fin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ 𝓢(V, ℂ))
    [FiniteDimensional ℂ N] : ∃ N' : Submodule ℂ 𝓢(V, ℂ), FiniteDimensional ℂ N' ∧ ∀ a L, ∀ f ∈ N, dop a L f ∈ N' := by
  let b := Module.finBasis ℝ (V × (V →L[ℝ] ℝ))
  refine ⟨⨆ i, N.map (dopL (b i).1 (b i).2), inferInstance, fun a L f hf => ?_⟩
  have : ∀ q ∈ Submodule.span ℝ (Set.range b), dop q.1 q.2 f ∈ ⨆ i, N.map (dopL (b i).1 (b i).2) := fun q hq => by
    induction hq using Submodule.span_induction with
    | mem q h => obtain ⟨i, rfl⟩ := h; exact Submodule.mem_iSup_of_mem i ⟨f, hf, rfl⟩
    | zero => convert Submodule.zero_mem _; ext x; simp [dop_apply]
    | add x y _ _ hx hy => rw [Prod.fst_add, Prod.snd_add, dop_add]; exact add_mem hx hy
    | smul t q _ h =>
      convert Submodule.smul_mem _ (t : ℂ) h
      ext x
      simp only [dop_apply, Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply,
        smul_eq_mul, Complex.real_smul]
      push_cast
      ring
  exact this (a, L) (b.span_eq ▸ trivial)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def vacSp (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) :
    Submodule ℂ (SInf F (Fin n × Fin d)) where
  carrier := {f | ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    dopL (aOf M u') (lOf M u') f = Complex.I • dopL (aOf M u) (lOf M u) f}
  zero_mem' _ _ _ _ _ := by simp
  add_mem' hf hg u u' h1 h2 h3 := by rw [map_add (f := _), map_add (f := _), hf u u' h1 h2 h3, hg u u' h1 h2 h3, smul_add]
  smul_mem' c f hf u u' h1 h2 h3 := by rw [map_smul, map_smul, hf u u' h1 h2 h3, smul_comm]

theorem vacSp_fin (h : IsCMExt F E σ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) :
    FiniteDimensional ℂ (vacSp M τ ε) := by
  let ev : SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ
  refine FiniteDimensional.of_injective (ev.toLinearMap ∘ₗ (vacSp M τ ε).subtype)
    ((injective_iff_map_eq_zero _).2 fun f h0 => Subtype.ext ?_)
  by_contra hf
  let C : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin d) ℂ := fun w =>
    { toFun := fun x => (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * x * (W.θ w)ᵀ)
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun t x => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        rw [smul_comm] }
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure σ h τ M.co.e C
  let T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y b => linForm b y) (fun y y' b => map_add _ y y') (fun t y b => map_smul _ t y)
      (fun y b b' => by simp only [linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
      (fun t y b => by simp only [linForm_apply, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.Twist.FockLogDeriv.main T (fun b hb => funext fun i => trace_mul_eq_zero _ fun y => by
      have : linForm b (Pi.single i y) = 0 := hb _
      rw [linForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this
      exact this) J f.1 hf fun p y => by
    have := congrArg (fun g : SInf F (Fin n × Fin d) => g y) (f.2 (S p) (S (J p)) (sAt _) (sAt _) fun w => sJ p w)
    simp only [dopL, LinearMap.coe_mk, AddHom.coe_mk, SchwartzMap.smul_apply, smul_eq_mul, dop_apply, aOf, lOf] at this
    rw [show aOf M (S p) = p.1 from (sev _).1, show aOf M (S (J p)) = (J p).1 from (sev _).1, (sev _).2, (sev _).2] at this
    exact this
  obtain ⟨c, Q, Q', hc, -, e⟩ := GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_gaussian f.1 hf m hm
  have : f.1 0 = 0 := h0
  rw [e] at this
  exact mul_ne_zero hc (Complex.exp_ne_zero _) this

variable {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W}

theorem vacSp_map (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {τ : ∀ w : InfinitePlace F, EmbOver E w} {k : UA σ X.J} (hk : k ∈ KInf σ X τ) {A} (hA : Impl om (k, 1) A) {ε f}
    (hf : f ∈ vacSp M τ ε) : A f ∈ vacSp M τ ε := by
  intro u u' hu hu' hrel
  have e0 : ∀ g v, actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) v = mat g * v := fun g v => by simp [actAB, mat]
  have e1 : mat k * mat k⁻¹ = 1 := by show k.1.1 * ((k⁻¹ : UA σ X.J).1.1) = 1; simp
  have e2 : mat k⁻¹ * mat k = 1 := by show ((k⁻¹ : UA σ X.J).1.1) * k.1.1 = 1; simp
  have a1 := at_act (W := W) (k⁻¹, 1) hu
  have a2 := at_act (W := W) (k⁻¹, 1) hu'
  have i1 := inter hψ hs hA a1 f
  have i2 := inter hψ hs hA a2 f
  simp only [e0, ← Matrix.mul_assoc, e1, Matrix.one_mul] at i1 i2 a1 a2
  have := hf _ _ a1 a2 fun w => by
    have h1 : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, e2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, e1, Matrix.map_one _ (map_zero _) (map_one _)]
    have hc : (mat k⁻¹).map (piInf (τ w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (τ w)) := by
      rw [← Matrix.one_mul (X.θ w * _), ← h1, Matrix.mul_assoc, ← Matrix.mul_assoc _ (X.θ w), (hk.2 w).eq, Matrix.mul_assoc,
        h2, Matrix.mul_one]
    rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.mul_smul]
    simp only [← Matrix.mul_assoc, hc]
  change dop _ _ _ = Complex.I • dop _ _ _ at this ⊢
  rw [← i1, ← i2, this, map_smul]

theorem pol_finite (h : IsCMExt F E σ) (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {f} (hf : f ∈ M.Pol ψ τ) :
    ∃ N : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ N ∧ f ∈ N ∧
      ∀ k ∈ KInf σ X τ, ∀ A, Impl om (k, 1) A → ∀ g ∈ N, A g ∈ N := by
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ N : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ N ∧ f ∈ N ∧
        ∀ k ∈ KInf σ X τ, ∀ A, Impl om (k, 1) A → ∀ g ∈ N, A g ∈ N}
      zero_mem' := ⟨⊥, inferInstance, zero_mem _, fun k _ A _ g hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1, h2⟩ ⟨N', _, h1', h2'⟩
        refine ⟨N ⊔ N', inferInstance, Submodule.add_mem_sup h1 h1', fun k hk A hA g hg => ?_⟩
        obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
        rw [map_add (f := _)]
        exact Submodule.add_mem_sup (h2 k hk A hA x hx) (h2' k hk A hA y hy)
      smul_mem' := fun c f ⟨N, h0, h1, h2⟩ => ⟨N, h0, N.smul_mem c h1, h2⟩ }
  refine (sInf_le (a := S) ⟨fun f₀ ⟨ε, hε⟩ => ?_, fun u hu g ⟨N, h0, h1, h2⟩ g₁ hg => ?_⟩ : M.Pol ψ τ ≤ S) hf
  · exact ⟨vacSp M τ ε, vacSp_fin h M τ ε, fun u u' hu hu' e => hε u u' hu hu' e _ _ (actsD_dop M hψ hu f₀)
      (actsD_dop M hψ hu' f₀), fun k hk A hA g hg => vacSp_map hψ hs hk hA hg⟩
  · obtain ⟨N', h3, h4⟩ := exists_dop_fin N
    refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = dop (aOf M v) (lOf M v) x},
      Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_),
      Submodule.subset_span ⟨u, hu, g, h1, actsD_unique' M hψ hu hg⟩, fun k hk A hA z hz => ?_⟩
    · rintro _ ⟨v, -, x, hx, rfl⟩
      exact h4 _ _ x hx
    · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap A.toLinearMap (Submodule.span ℂ
        {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = dop (aOf M v) (lOf M v) x}))).2 ?_ hz)
      rintro _ ⟨v, hv, x, hx, rfl⟩
      exact Submodule.subset_span ⟨_, at_act _ hv, _, h2 k hk A hA x hx, inter hψ hs hA hv x⟩

end Dense

theorem realInv_of (hA : PositivityTheory.ThKF.ArchOp) : RealInv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp _ P _ _ _ p hq
  obtain ⟨f, hf, h0⟩ : ∃ f ∈ M.Pol B.ψ B.emb, p f ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_ne (0 : P)
    obtain ⟨f, hf, rfl⟩ : y ∈ (M.Pol B.ψ B.emb).map p := hq.onto ▸ trivial
    exact ⟨f, hf, hy⟩
  have hs := hp.weil.isUSplitting
  obtain ⟨N, _, h1, h2⟩ := Dense.pol_finite hp.base.cm hp.base.std hs.toIsSplitting B.emb hf
  haveI : FiniteDimensional ℂ (N ⊓ M.Pol B.ψ B.emb : Submodule ℂ _) := Submodule.finiteDimensional_of_le inf_le_left
  haveI := Dense.volume_isAddHaar F (Fin n × Fin d)
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨f₀, hf₀, hne, hfix⟩ := Dense.exists_fixed
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F))).toLinearMap
    (SchwartzMap.injective_toLp 2 _) p (N ⊓ M.Pol B.ψ B.emb) ⟨h1, hf⟩ h0
  refine ⟨f₀, hf₀.2, hne, fun k hk => ?_⟩
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evI F) := fun u _ => by simp [mat]
  obtain ⟨T, hT, hP⟩ := hA F E σ B n d X W M χX χW om r s r' s' hp k hk.1 1 h1W
  have hP' := hP hk ⟨h1W, fun w => by simp [mat]⟩
  have hn := Dense.lintegral_eq (S := om (k, 1)) (fun μ hμ => hs.unit μ hμ (k, 1)) (hT.1 f₀)
  have := hfix (T f₀) ⟨h2 k hk T hT.1 _ hf₀.1, hP' _ hf₀.2⟩ (hq.cpt k hk f₀ hf₀.2 _ (hT.2 f₀)) (by
    change ‖(T f₀).toLp 2 _‖ = ‖f₀.toLp 2 _‖
    simp only [SchwartzMap.norm_toLp, eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top (T f₀).continuous.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top f₀.continuous.aestronglyMeasurable,
      ENNReal.toReal_ofNat, ENNReal.rpow_two, hn])
  simpa only [this] using hT.2 f₀

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.RegOfBound
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.An

open Filter Topology Metric
open scoped BoundedContinuousFunction

variable {X : Type} {h : X → ℝ}

theorem unif_bound (h1 : ∀ x, 1 ≤ h x) {V : Submodule ℂ (X → ℂ)} (hV : ∀ f ∈ V, ∃ (C : ℝ) (N : ℕ), ∀ x, ‖f x‖ ≤ C * h x ^ N)
    {D : Set ℂ} {H : ℂ → V} (hb : ∀ μ : V →ₗ[ℂ] ℂ, (∀ N : ℕ, ∃ C : ℝ, ∀ f : V, (∀ x, ‖f.1 x‖ ≤ h x ^ N) → ‖μ f‖ ≤ C) →
      ∃ C, ∀ s ∈ D, ‖μ (H s)‖ ≤ C) : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ D, ∀ x, ‖(H s).1 x‖ ≤ C * h x ^ N := by
  by_contra hn
  push Not at hn
  choose s hs g hg using fun n : ℕ => hn (n * 2 ^ n) n
  have h0 : ∀ x, 0 < h x := fun x => one_pos.trans_le (h1 x)
  let w : ℕ → ℝ := fun n => (1 / 2) ^ n / h (g n) ^ n
  have w0 : ∀ n, 0 < w n := fun n => div_pos (by positivity) (pow_pos (h0 _) _)
  have est : ∀ N : ℕ, ∃ K : ℝ, ∀ (f : X → ℂ) (C : ℝ), (∀ x, ‖f x‖ ≤ C * h x ^ N) → ∀ (c : ℕ →ᵇ ℂ) n,
      ‖c n * (w n * f (g n))‖ ≤ C * K * ‖c‖ * (1 / 2) ^ n := fun N => by
    refine ⟨1 + ∑ m ∈ Finset.range N, h (g m) ^ N, fun f C hf c n => ?_⟩
    have C0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hf (g n))) (pow_pos (h0 _) _)
    have S0 : 0 ≤ ∑ m ∈ Finset.range N, h (g m) ^ N := Finset.sum_nonneg fun m _ => (pow_pos (h0 _) _).le
    have k : h (g n) ^ N / h (g n) ^ n ≤ 1 + ∑ m ∈ Finset.range N, h (g m) ^ N := by
      by_cases hN : n < N
      · refine (div_le_self (pow_pos (h0 _) _).le (one_le_pow₀ (h1 _))).trans (le_add_of_nonneg_of_le zero_le_one ?_)
        exact Finset.single_le_sum (f := fun m => h (g m) ^ N) (fun m _ => (pow_pos (h0 _) _).le) (Finset.mem_range.2 hN)
      · exact ((div_le_one (pow_pos (h0 _) _)).2 (pow_le_pow_right₀ (h1 _) (not_lt.1 hN))).trans (le_add_of_nonneg_right S0)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (w0 n).le]
    calc _ ≤ ‖c‖ * (w n * (C * h (g n) ^ N)) := by gcongr; exacts [mul_nonneg (w0 n).le (norm_nonneg _), c.norm_coe_le_norm n, (w0 n).le, hf _]
      _ = C * (h (g n) ^ N / h (g n) ^ n) * ‖c‖ * (1 / 2) ^ n := by simp only [w]; ring
      _ ≤ _ := by gcongr
  have sm : ∀ (f : V) (c : ℕ →ᵇ ℂ), Summable fun n => c n * (w n * f.1 (g n)) := fun f c => by
    obtain ⟨C, N, hf⟩ := hV f.1 f.2
    obtain ⟨K, hK⟩ := est N
    exact .of_norm_bounded (summable_geometric_two.mul_left _) (hK f C hf c)
  have bd : ∀ N : ℕ, ∃ K : ℝ, ∀ (f : X → ℂ) (C : ℝ), (∀ x, ‖f x‖ ≤ C * h x ^ N) → ∀ c : ℕ →ᵇ ℂ,
      ‖∑' n, c n * (w n * f (g n))‖ ≤ C * K * 2 * ‖c‖ := fun N => (est N).imp fun K hK f C hf c =>
    (tsum_of_norm_bounded (hasSum_geometric_two.mul_left _) (hK f C hf c)).trans_eq (by ring)
  let B : V →ₗ[ℂ] (ℕ →ᵇ ℂ) →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun f c => ∑' n, c n * (w n * f.1 (g n)))
    (fun f f' c => by rw [← (sm f c).tsum_add (sm f' c)]; simp [mul_add])
    (fun a f c => by rw [smul_eq_mul, ← tsum_mul_left]; exact tsum_congr fun n => by simp; ring)
    (fun f c c' => by rw [← (sm f c).tsum_add (sm f c')]; simp [add_mul])
    (fun a f c => by rw [smul_eq_mul, ← tsum_mul_left]; exact tsum_congr fun n => by simp; ring)
  have ct : ∀ f : V, ∃ C, ∀ c, ‖B f c‖ ≤ C * ‖c‖ := fun f => by
    obtain ⟨C, N, hf⟩ := hV f.1 f.2
    obtain ⟨K, hK⟩ := bd N
    exact ⟨_, hK f C hf⟩
  obtain ⟨M, hM⟩ := banach_steinhaus (g := fun n : ℕ => (B (H (s n))).mkContinuousOfExistsBound (ct _)) fun c => by
    obtain ⟨C, hC⟩ := hb (B.flip c) fun N => (bd N).elim fun K hK => ⟨_, fun f hf => hK f 1 (by simpa using hf) c⟩
    exact ⟨C, fun n => hC _ (hs n)⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max M 0)
  let c : ℕ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (Pi.single n 1) 1 fun m => by
    by_cases e : m = n <;> simp [e]
  have c1 : ‖c‖ ≤ 1 := (BoundedContinuousFunction.norm_le zero_le_one).2 fun m => by by_cases e : m = n <;> simp [c, e]
  have e1 : ‖B (H (s n)) c‖ ≤ max M 0 :=
    (ContinuousLinearMap.le_of_opNorm_le _ ((hM n).trans (le_max_left M 0)) c).trans (mul_le_of_le_one_right (le_max_right _ _) c1)
  have e2 : B (H (s n)) c = w n * (H (s n)).1 (g n) :=
    (tsum_eq_single n fun m e => by simp [c, e]).trans (by simp [c])
  rw [e2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (w0 n).le] at e1
  have e3 : w n * (n * 2 ^ n * h (g n) ^ n) = n := by
    have := (h0 (g n)).ne'
    simp only [w, one_div, inv_pow]; field_simp
  linarith [mul_lt_mul_of_pos_left (hg n) (w0 n)]

variable [TopologicalSpace X] {g g' : ℂ → X → ℂ} {S S' : Set ℂ} {s₀ : ℂ}


variable (h g S) in
structure RegOn : Prop where
  hol : ∀ x, DifferentiableOn ℂ (g · x) S
  cont : ContinuousOn (fun y : ℂ × X => g y.1 y.2) (S ×ˢ Set.univ)
  grow : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ S, ∀ x, ‖g s x‖ ≤ C * h x ^ N


variable (h g s₀) in
def Reg : Prop := ∃ S ∈ 𝓝 s₀, RegOn h g S

theorem RegOn.mono (a : RegOn h g S) (e : S' ⊆ S) : RegOn h g S' :=
  ⟨fun x => (a.hol x).mono e, a.cont.mono (Set.prod_mono e subset_rfl), a.grow.imp fun _ => .imp fun _ b s hs => b s (e hs)⟩

theorem Reg.congr (a : Reg h g s₀) (e : g' =ᶠ[𝓝 s₀] g) : Reg h g' s₀ := by
  obtain ⟨S, hS, a⟩ := a
  have b := a.mono (Set.inter_subset_left (t := {s | g' s = g s}))
  exact ⟨_, inter_mem hS e, fun x => (b.hol x).congr fun s hs => congrFun hs.2 x, b.cont.congr fun y hy => congrFun hy.1.2 y.2,
    b.grow.imp fun _ => .imp fun _ b s hs x => by rw [hs.2]; exact b s hs x⟩

theorem Reg.eventually (a : Reg h g s₀) : ∀ᶠ s in 𝓝 s₀, Reg h g s :=
  let ⟨S, hS, a⟩ := a
  (eventually_mem_nhds_iff.2 hS).mono fun _ hs => ⟨S, hs, a⟩

theorem Reg.contAt (a : Reg h g s₀) (x : X) : ContinuousAt (fun y : ℂ × X => g y.1 y.2) (s₀, x) :=
  let ⟨_, hS, a⟩ := a
  a.cont.continuousAt (prod_mem_nhds hS univ_mem)

theorem Reg.mul (h1 : ∀ x, 1 ≤ h x) (a : Reg h g s₀) {c : ℂ → ℂ} (hc : AnalyticAt ℂ c s₀) {u : X → X} (hu : Continuous u) {b : ℝ}
    (hb : ∀ x, h (u x) ≤ b * h x) : Reg h (fun s x => c s * g s (u x)) s₀ := by
  obtain ⟨S, hS, a⟩ := a
  have e : ∀ᶠ s in 𝓝 s₀, ‖c s‖ < ‖c s₀‖ + 1 := hc.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨_, inter_mem hS (hc.eventually_analyticAt.and e), fun x => DifferentiableOn.mul
    (fun s hs => hs.2.1.differentiableAt.differentiableWithinAt) ((a.hol (u x)).mono Set.inter_subset_left),
    ContinuousOn.mul (fun y hy => (hy.1.2.1.continuousAt.comp continuous_fst.continuousAt).continuousWithinAt)
      (a.cont.comp (f := fun y : ℂ × X => (y.1, u y.2)) (by fun_prop) fun y hy => ⟨hy.1.1, trivial⟩), ?_⟩
  obtain ⟨C, N, hC⟩ := a.grow
  refine ⟨(‖c s₀‖ + 1) * (max C 0 * b ^ N), N, fun s hs x => ?_⟩
  have h0 := zero_le_one.trans (h1 (u x))
  rw [norm_mul, mul_assoc, mul_assoc, ← mul_pow]
  exact mul_le_mul hs.2.2.le ((hC s hs.1 _).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ h0 (hb x) N) (pow_nonneg h0 _)
    (le_max_right _ _))) (norm_nonneg _) (by positivity)

theorem reg_of_bound (hh : Continuous h) (hS : S ∈ 𝓝 s₀) (hd : ∀ x, DifferentiableOn ℂ (g · x) S) (hc : ∀ s ∈ S, Continuous (g s))
    (hg : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ S, ∀ x, ‖g s x‖ ≤ C * h x ^ N) : Reg h g s₀ := by
  refine ⟨interior S, interior_mem_nhds.2 hS, fun x => (hd x).mono interior_subset, fun y hy => ContinuousAt.continuousWithinAt ?_,
    hg.imp fun _ => .imp fun _ b s hs => b s (interior_subset hs)⟩
  obtain ⟨C, N, hC⟩ := hg
  obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy.1)
  have : Tendsto (fun z : ℂ × X => g z.1 z.2 - g y.1 z.2) (𝓝 y) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun z => 2 * (C * h z.2 ^ N) / r * dist z.1 y.1) ?_ ?_
    · filter_upwards [continuous_fst.continuousAt.eventually (ball_mem_nhds y.1 r0)] with z hz
      rw [← dist_eq_norm]
      refine Complex.dist_le_div_mul_dist_of_mapsTo_ball (f := (g · z.2)) ((hd z.2).mono hr) (fun s hs => ?_) hz
      rw [mem_closedBall, dist_eq_norm, two_mul]
      exact (norm_sub_le _ _).trans (add_le_add (hC s (hr hs) _) (hC _ (hr (mem_ball_self r0)) _))
    · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  simpa [ContinuousAt] using this.add ((hc _ (interior_subset hy.1)).comp continuous_snd).continuousAt

theorem Reg.punct (h1 : ∀ x, 1 ≤ h x) {k : ℕ} (a : Reg h g' s₀) (e : ∀ᶠ s in 𝓝[≠] s₀, ∀ x, g' s x = (s - s₀) ^ k * g s x) :
    ∀ᶠ s in 𝓝[≠] s₀, Reg h g s := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds a.eventually, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (eventually_nhdsWithin_iff.1 e).eventually_nhds] with s b hs e
  refine (b.mul h1 (c := fun z => ((z - s₀) ^ k)⁻¹) (AnalyticAt.inv (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hs)))
    continuous_id (b := 1) (by simp)).congr ?_
  filter_upwards [e, isOpen_ne.mem_nhds hs] with z hz hz'
  funext x
  rw [id, hz hz', inv_mul_cancel_left₀ (pow_ne_zero _ (sub_ne_zero.2 hz'))]

theorem Reg.remove (h1 : ∀ x, 1 ≤ h x) {k : ℕ} (a : Reg h g' s₀) (e : ∀ᶠ s in 𝓝[≠] s₀, ∀ x, g' s x = (s - s₀) ^ k * g s x)
    (hS : S ∈ 𝓝 s₀) (hd : ∀ x, DifferentiableOn ℂ (g · x) S) : Reg h g s₀ := by
  obtain ⟨S', hS', b⟩ := id a
  obtain ⟨ρ, ρ0, hρ⟩ := nhds_basis_closedBall.mem_iff.1
    (inter_mem (inter_mem hS hS') (eventually_nhdsWithin_iff.1 (e.and (a.punct h1 e))))
  have dc : ∀ x, DiffContOnCl ℂ (g · x) (ball s₀ ρ) := fun x => (hd x).diffContOnCl_ball fun z hz => (hρ hz).1.1
  have sp : ∀ z ∈ sphere s₀ ρ, z ≠ s₀ := fun z hz => ne_of_mem_sphere hz ρ0.ne'
  obtain ⟨C, N, hC⟩ := b.grow
  refine ⟨_, ball_mem_nhds s₀ ρ0, fun x => (dc x).differentiableOn, fun y hy => ContinuousAt.continuousWithinAt ?_, C / ρ ^ k, N,
    fun z hz x => Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball (dc x) (fun w hw => ?_) (subset_closure hz)⟩
  · by_cases e0 : y.1 = s₀
    · rw [show y = (s₀, y.2) from Prod.ext e0 rfl]
      exact contAt_of_sphere ρ0 dc (fun z hz => (((hρ (sphere_subset_closedBall hz.1)).2 (sp _ hz.1)).2.contAt z.2).continuousWithinAt) _
    · exact ((hρ (ball_subset_closedBall hy.1)).2 e0).2.contAt y.2
  · rw [frontier_ball _ ρ0.ne'] at hw
    have c := hρ (sphere_subset_closedBall hw)
    have := hC w c.1.2 x
    rw [(c.2 (sp w hw)).1, norm_mul, norm_pow, mem_sphere_iff_norm.1 hw] at this
    rw [div_mul_eq_mul_div, le_div_iff₀' (pow_pos ρ0 k)]
    exact this

theorem preconn {U : Set ℂ} (hU : ∀ s, ∀ᶠ z in 𝓝[≠] s, z ∈ U) : IsPreconnected U := by
  obtain ⟨t, ht, -, hc⟩ := isLindelof_univ.elim_nhds_subcover (fun s => insert s U) fun s _ => insert_mem_nhds_iff.2 (hU s)
  have : (Uᶜ).Countable := ht.mono fun z hz => by
    obtain ⟨s, hs, e⟩ := Set.mem_iUnion₂.1 (hc (Set.mem_univ z))
    exact e.resolve_right hz ▸ hs
  simpa using (this.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected

end GlobalTheory.ThK.Dbl.An

end
end

