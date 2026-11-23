module

public import Mathlib
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieE
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieF

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieG
section
noncomputable section

open scoped TensorProduct Matrix Classical RealInnerProductSpace Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealWeil Complex

namespace PositivityTheory.RL.Up

section Inv

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [Fintype β]

theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hTens_actB [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB) (x y : Matrix α β E) :
    hTens c JA JB (actB c g x) (actB c g y) = hTens c JA JB x y := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c = JB := g.2
  rw [hTens_eq, hTens_eq]
  have : actB c g x * JB * ((actB c g y).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    unfold actB
    rw [show (y * ((g : GL β E) : Matrix β β E)ᵀ).map c = y.map c * (((g : GL β E) : Matrix β β E)ᵀ).map c from
      Matrix.map_mul (f := c.toRingHom), Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    conv_rhs => rw [← hg]
    simp only [Matrix.mul_assoc]
  rw [this]

end Inv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ext_at (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m n : Type} {X X' : Matrix m n (AE F E)}
    (hx : At (evI F) (X - X')) (hinf : ∀ w, X.map (piInf (τ w)) = X'.map (piInf (τ w))) : X = X' := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf h τ _ (fun u hu => congrFun (congrFun (hx u hu) i) j) fun w => ?_)
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun (hinf w) i) j

theorem At.sub' {M : Type} [AddCommGroup M] [Module (AF F) M] {a b : M} (ha : At (evI F) a) (hb : At (evI F) b) :
    At (evI F) (a - b) := fun u hu => by rw [smul_sub, ha u hu, hb u hu, sub_zero]

theorem exists_lf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (m n : Type) :
    ∃ L : (InfinitePlace F → Matrix m n ℂ) → Matrix m n (AE F E), Continuous L ∧ (∀ z, At (evI F) (L z)) ∧
      ∀ z w, (L z).map (piInf (τ w)) = z w := by
  obtain ⟨s, hs, hs'⟩ := exists_section h τ
  refine ⟨fun z => Matrix.of fun i j => s fun w => z w i j,
    continuous_matrix fun i j => hs.comp (continuous_pi fun w => (continuous_apply w).matrix_elem i j),
    fun z a ha => ?_, fun z w => ?_⟩
  · ext i j
    exact (hs' _).1 a ha
  · ext i j
    exact (hs' _).2 w

variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

theorem exists_iota (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E))
    (K : InfinitePlace F → Matrix β β ℂ)
    (hK : ∀ w (g : Matrix β β ℂ), gᴴ * K w * g = K w → gᵀ * J.map (piInf (τ w)) * g.map star = J.map (piInf (τ w))) :
    ∃ ι : SG K →* UG (cA σ) J, Continuous ι ∧ (∀ g, At (evI F) (((ι g).1 : Matrix β β (AE F E)) - 1)) ∧
      ∀ g w, ((ι g).1 : Matrix β β (AE F E)).map (piInf (τ w)) = g.1.1 w := by
  obtain ⟨L, hc, hL, hL'⟩ := exists_lf h τ β β
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hG : ∀ (a : InfinitePlace F → Matrix β β ℂ) w, (1 + L (a - 1)).map (piInf (τ w)) = a w := fun a w => by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), hL']
    simp
  let G : (InfinitePlace F → Matrix β β ℂ) →* Matrix β β (AE F E) :=
    { toFun := fun a => 1 + L (a - 1)
      map_one' := ext_at h τ (fun u hu => by rw [add_sub_cancel_left, hL _ u hu]) fun w => by
        rw [hG, Matrix.map_one _ (map_zero _) (map_one _)]
        rfl
      map_mul' := fun a c => ext_at h τ (fun u hu => by
        have e : (1 + L (a * c - 1)) - (1 + L (a - 1)) * (1 + L (c - 1)) =
            L (a * c - 1) - L (c - 1) - L (a - 1) * (1 + L (c - 1)) := by noncomm_ring
        rw [e, smul_sub, smul_sub, ← Matrix.smul_mul, hL _ u hu, hL _ u hu, hL _ u hu]
        simp) fun w => by
        rw [Matrix.map_mul, hG, hG, hG]
        rfl }
  have hGc : Continuous G := continuous_const.add (hc.comp (continuous_id.sub continuous_const))
  have hGU : ∀ g : SG K, (G g.1.1)ᵀ * J * (G g.1.1).map (cA σ) = J := fun g => by
    refine ext_at h τ (fun u hu => ?_) fun w => ?_
    · set N := L (g.1.1 - 1)
      have hN : u • N = 0 := hL _ u hu
      have e0 : (G g.1.1).map (cA σ) = 1 + N.map (cA σ) := by
        show (1 + N).map _ = _
        rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
      have e : (G g.1.1)ᵀ * J * (G g.1.1).map (cA σ) - J = Nᵀ * (J * (G g.1.1).map (cA σ)) + J * N.map (cA σ) := by
        rw [e0]
        show (1 + N)ᵀ * _ * _ - _ = _
        simp only [Matrix.transpose_add, Matrix.transpose_one]
        noncomm_ring
      have e1 : u • N.map (cA σ) = 0 := by
        ext i j
        have := congrArg (cA σ) (congrFun (congrFun hN i) j)
        simpa using this
      rw [e, smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, e1, ← Matrix.transpose_smul, hN]
      simp
    · rw [map_form h, show (G g.1.1).map (piInf (τ w)) = _ from hG _ w]
      exact hK w _ (congrFun (show star g.1.1 * K * g.1.1 = K from g.2) w)
  refine ⟨((Units.map G).comp (SG K).subtype).codRestrict _ hGU,
    ((Continuous.units_map G hGc).comp continuous_subtype_val).subtype_mk _, fun g u hu => ?_, fun g w => hG _ w⟩
  show u • (1 + L (g.1.1 - 1) - 1) = 0
  rw [add_sub_cancel_left, hL _ u hu]


variable (σ) in
def sB (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (u v : Matrix α β (AE F E)) : ℝ :=
  -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u v))

def IsD {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)) : Prop :=
  ∀ u, At (evI F) u → ∀ f x, D u f x = fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x

variable {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}

theorem at_e {u : Matrix α β (AE F E)} (hu : At (evI F) u) : At (evI F) (d.e u) := fun s hs => by
  rw [← map_smul, hu s hs, map_zero]

theorem at_symm {p} (hp : At (evI F) p) : At (evI F) (d.e.symm p) := fun s hs => by
  rw [← map_smul, hp s hs, map_zero]

theorem sympl_e {l : Type} [Fintype l] (c : Co F κ l) (u v : Matrix α β (AE F E)) :
    sympl (c.vec (d.e u)) (c.vec (d.e v)) = sB σ JA JB u v := by
  rw [c.sympl_vec, sB, d.form]

theorem IsD.P {D} (hD : IsD d D) {l : Type} [Fintype l] (c : Co F κ l) {u : Matrix α β (AE F E)} (hu : At (evI F) u)
    (f : Sch l) : c.P (dRho (c.vec (d.e u)) f) = D u (c.P f) := by
  ext x
  rw [c.P_dRho, hD u hu]

theorem IsD.comm {D} (hD : IsD d D) {u v : Matrix α β (AE F E)} (hu : At (evI F) u) (hv : At (evI F) v) (f : SInf F κ) :
    D u (D v f) = D v (D u f) + (2 * π * I * sB σ JA JB u v) • f := by
  obtain ⟨n, ⟨c⟩⟩ := exists_co F κ
  have := congrArg (fun L => c.P (L (c.P' f))) (dRho_comm (c.vec (d.e u)) (c.vec (d.e v)))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, map_sub, map_smul, hD.P c hu, hD.P c hv, c.P_P', sympl_e] at this
  rw [← this]
  abel

end PositivityTheory.RL.Up

end
end

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieI
section
noncomputable section

open scoped TensorProduct Matrix Classical Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex MeasureTheory

namespace PositivityTheory.RL.Up

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem box_SB {g g' : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (hg' : g' ∈ SB (κ → Af F)) :
    boxFun g g' ∈ SB (κ ⊕ κ → Af F) := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  refine ⟨(hg.1.comp_continuous (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inl) (by fun_prop)).mul
    (hg'.1.comp_continuous (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inr) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((hg.2.prod hg'.2).image
    (Homeomorph.sumArrowHomeomorphProdArrow (ι := κ) (ι' := κ) (X := Af F)).symm.continuous) fun x hx => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  exact hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, Sum.elim_comp_inl_inr x⟩

variable (F κ) in
theorem exists_box : ∃ (f : SInf F κ) (B : SInf F (κ ⊕ κ)) (r : (κ → mixedEmbedding.mixedSpace F) → ℝ),
    (∀ x, B x = f (x ∘ Sum.inl) * f (x ∘ Sum.inr)) ∧ (∀ x, f x = r x) ∧ Continuous r ∧ HasCompactSupport r ∧ r 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, by norm_num, by norm_num⟩
  have h1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := ofRealCLM.contDiff.comp b.contDiff
  have h3 : HasCompactSupport fun x : κ ⊕ κ → mixedEmbedding.mixedSpace F =>
      ((b (x ∘ Sum.inl) : ℝ) : ℂ) * ((b (x ∘ Sum.inr) : ℝ) : ℂ) := by
    refine HasCompactSupport.intro ((h1.prod h1).image
      (Homeomorph.sumArrowHomeomorphProdArrow (ι := κ) (ι' := κ) (X := mixedEmbedding.mixedSpace F)).symm.continuous)
      fun x hx => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    exact hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, Sum.elim_comp_inl_inr x⟩
  exact ⟨h1.toSchwartzMap h2, h3.toSchwartzMap ((h2.comp (contDiff_pi.2 fun i => contDiff_apply ℝ _ (Sum.inl i))).mul
    (h2.comp (contDiff_pi.2 fun i => contDiff_apply ℝ _ (Sum.inr i)))), b, fun _ => rfl, fun _ => rfl, b.continuous,
    b.hasCompactSupport, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)⟩

variable (F κ) in
theorem exists_form (ψ : AddChar (AF F) ℂ) : ∃ l ∈ (adeleClass F).adm (κ ⊕ κ),
    (∀ x y : κ → AF F, ∀ φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ) ∧
      ∃ (B : SInf F (κ ⊕ κ)), ∃ G ∈ SB (κ ⊕ κ → Af F), l (pureA F B G) ≠ 0 := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  borelize (κ → Af F)
  let X := κ → mixedEmbedding.mixedSpace F
  borelize X
  let μ : Measure X := Measure.addHaar
  let ν : Measure (κ → Af F) := Measure.addHaar
  haveI : MeasurableAdd X := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → Af F) := ContinuousAdd.measurableAdd
  haveI : (μ.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ ν
  let k : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] (X × (κ → Af F) → ℂ) :=
    LinearMap.funLeft ℂ ℂ fun p => Sum.elim (SeminormBoundRestriction.pt p.1 p.2) (SeminormBoundRestriction.pt p.1 p.2)
  let N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { carrier := {φ | Integrable (k φ) (μ.prod ν)}
      zero_mem' := integrable_zero _ _ _
      add_mem' := fun ha hb => ha.add hb
      smul_mem' := fun c _ h => h.smul c }
  let l0 : N →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ p, k φ p ∂(μ.prod ν)
      map_add' := fun a b => integral_add a.2 b.2
      map_smul' := fun c a => integral_smul c _ }
  obtain ⟨l, hl⟩ := l0.exists_extend
  have hl' : ∀ φ ∈ N, l φ = ∫ p, k φ p ∂(μ.prod ν) := fun φ h => LinearMap.congr_fun hl ⟨φ, h⟩
  let dg : X →L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.elim id id i)
  have hdg : AntilipschitzWith 1 dg := AddMonoidHomClass.antilipschitz_of_bound dg fun x => by
    rw [NNReal.coe_one, one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (dg x) (Sum.inl i)
  let Rs : SInf F (κ ⊕ κ) →L[ℂ] 𝓢(X, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ dg.hasTemperateGrowth hdg
  have hk : ∀ (B : SInf F (κ ⊕ κ)) (G : (κ ⊕ κ → Af F) → ℂ),
      k (pureA F B G) = fun p => Rs B p.1 * G (Sum.elim p.2 p.2) := fun B G => by
    funext p
    refine congrArg₂ (· * ·) (congrArg B (funext fun i => ?_)) (congrArg G (funext fun i => ?_))
    · rcases i with i | i <;> exact RingEquiv.apply_symm_apply _ _
    · rcases i with i | i <;> rfl
  have hc : Continuous fun b : κ → Af F => (Sum.elim b b : κ ⊕ κ → Af F) :=
    continuous_pi fun i => by rcases i with i | i <;> exact continuous_apply i
  have hG : ∀ G ∈ SB (κ ⊕ κ → Af F), Integrable (fun b : κ → Af F => G (Sum.elim b b)) ν := fun G hG =>
    (hG.1.continuous.comp hc).integrable_of_hasCompactSupport (hG.2.comp_isClosedEmbedding
      (Function.LeftInverse.isClosedEmbedding (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inl) (fun _ => rfl) (by fun_prop) hc))
  have hp : ∀ (B : SInf F (κ ⊕ κ)), ∀ G ∈ SB (κ ⊕ κ → Af F), pureA F B G ∈ N := fun B G h => by
    show Integrable (k _) _
    rw [hk]
    exact (Rs B).integrable.mul_prod (hG G h)
  have hv : ∀ (B : SInf F (κ ⊕ κ)), ∀ G ∈ SB (κ ⊕ κ → Af F),
      l (pureA F B G) = (∫ a, Rs B a ∂μ) * ∫ b, G (Sum.elim b b) ∂ν := fun B G h => by
    rw [hl' _ (hp B G h), hk]
    exact integral_prod_mul (Rs B) fun b => G (Sum.elim b b)
  refine ⟨l, fun G h => ⟨(∫ b, G (Sum.elim b b) ∂ν) • (SchwartzMap.integralCLM ℂ μ ∘L Rs), fun B => ?_⟩,
    fun x y φ hφ => ?_, ?_⟩
  · rw [hv B G h, mul_comm]
    rfl
  · have hN : φ ∈ N := (Submodule.span_le.2 (by rintro _ ⟨B, G, h, rfl⟩; exact hp B G h) : schA F (κ ⊕ κ) ≤ N) hφ
    let c : X × (κ → Af F) := (fun i => evI F (x i), fun i => (x i).2)
    have e : k (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = fun p => k φ (c + p) := by
      funext p
      have e1 : SeminormBoundRestriction.pt (c + p).1 (c + p).2 = SeminormBoundRestriction.pt p.1 p.2 + x := funext fun i =>
        Prod.ext (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_add _ _).trans ((add_comm _ _).trans
          (congrArg (_ + ·) (RingEquiv.symm_apply_apply _ _)))) (add_comm _ _)
      show schr _ _ _ (Sum.elim (SeminormBoundRestriction.pt p.1 p.2) (SeminormBoundRestriction.pt p.1 p.2)) =
        φ (Sum.elim (SeminormBoundRestriction.pt (c + p).1 (c + p).2) (SeminormBoundRestriction.pt (c + p).1 (c + p).2))
      rw [e1, schr, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
      simp only [dotProduct_neg, add_neg_cancel, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
      congr 1
      funext i
      rcases i with i | i <;> rfl
    rw [hl' _ hN, hl' _ (by
      show Integrable (k _) _
      rw [e]
      exact (show Integrable (k φ) (μ.prod ν) from hN).comp_add_left c), e]
    exact integral_add_left_eq_self (k φ) c
  · obtain ⟨f, B, r, hB, hf, hr, hr', hr0⟩ := exists_box F κ
    obtain ⟨g, hg, y, hy⟩ := SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
    have hg' : (fun x => ((‖g x‖ : ℝ) : ℂ)) ∈ SB (κ → Af F) :=
      ⟨hg.1.comp fun z => ((‖z‖ : ℝ) : ℂ), hg.2.comp_left (g := fun z => ((‖z‖ : ℝ) : ℂ)) (by simp)⟩
    refine ⟨B, _, box_SB hg' hg', ?_⟩
    rw [hv _ _ (box_SB hg' hg')]
    refine mul_ne_zero ?_ ?_
    · have : ∀ a, Rs B a = ((r a * r a : ℝ) : ℂ) := fun a => by
        rw [ofReal_mul, ← hf]
        exact hB _
      simp only [this]
      rw [integral_complex_ofReal, ofReal_ne_zero]
      exact ((hr.mul hr).integral_pos_of_hasCompactSupport_nonneg_nonzero hr'.mul_left (fun _ => mul_self_nonneg _)
        (x := 0) (by simp [hr0])).ne'
    · have : ∀ b, boxFun (fun x => ((‖g x‖ : ℝ) : ℂ)) (fun x => ((‖g x‖ : ℝ) : ℂ)) (Sum.elim b b) =
          ((‖g b‖ * ‖g b‖ : ℝ) : ℂ) := fun b => (ofReal_mul _ _).symm
      simp only [this]
      rw [integral_complex_ofReal, ofReal_ne_zero]
      exact ((hg.1.continuous.norm.mul hg.1.continuous.norm).integral_pos_of_hasCompactSupport_nonneg_nonzero
        hg.2.norm.mul_left (fun _ => mul_self_nonneg _) (x := y) (by simp [hy])).ne'

end PositivityTheory.RL.Up

end
end

