module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RatAnnih

section Scalar

variable {F : Type} [Field F] [NumberField F]

theorem inf_rat (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ)) (y : Ainf F)
    (h : ∀ c : 𝓞 F, ∃ n : ℤ, L (y * algebraMap F _ (c : F)) = n) : ∃ d : F, y = algebraMap F _ d := by
  classical
  have hb : ∀ i, ∃ n : ℤ, L (y * algebraMap F _ (integralBasis F i)) = n := fun i => by
    rw [integralBasis_apply]; exact h _
  choose n hn using hb
  refine ⟨∑ i, (n i : F) * (integralBasis F).traceDual i, funext fun v => ?_⟩
  let φ : Ainf F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding v).comp (Pi.evalRingHom _ v)
  have hφ : Continuous φ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
  have key : (fun w : Ainf F => φ w) = fun w => ∑ i, L (w * algebraMap F _ (integralBasis F i)) *
      φ (algebraMap F _ ((integralBasis F).traceDual i)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hφ
      (continuous_finsetSum _ fun i _ => (hL.comp (continuous_id.mul continuous_const)).mul continuous_const) ?_
    funext x
    simp only [Function.comp_apply, ← map_mul, hT]
    conv_lhs => rw [← (integralBasis F).traceDual.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul,
      eq_ratCast]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← RingHom.comp_apply φ (algebraMap F (Ainf F)), map_ratCast]
  apply (InfinitePlace.Completion.extensionEmbedding v).injective
  change φ y = φ (algebraMap F (Ainf F) _)
  rw [congrFun key y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hn, map_sum, map_mul, map_intCast]

theorem fin_eq_zero {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (hv : ∀ v, ∃ y, psiV F ψ v y ≠ 1) (l : Af F)
    (h : ∀ c : F, ψ (pairA F 0 (l * algebraMap F _ c)) = 1) : l = 0 := by
  classical
  have hp : Continuous fun y : Af F => pairA F 0 (l * y) :=
    Continuous.prodMk continuous_const (continuous_const.mul continuous_id)
  have hall : ∀ z : Af F, ψ (pairA F 0 (l * z)) = 1 := by
    intro z
    obtain ⟨x, β, hβ, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 z
    have h1 : ψ (pairA F 0 (l * β)) = 1 :=
      GlobalTheory.IntDense.mem_of_isClosed F (C := {y | ψ (pairA F 0 (l * y)) = 1})
        (isClosed_eq (hψ.comp hp) continuous_const) (fun a => h a) β hβ
    have e : pairA F 0 (l * (algebraMap F _ x + 1 • β)) =
        pairA F 0 (l * algebraMap F _ x) + pairA F 0 (l * β) := by
      rw [one_smul, mul_add]
      exact Prod.ext (add_zero _).symm rfl
    rw [e, ψ.map_add_eq_mul, h, h1, one_mul]
  have hext : ∀ a b : Af F, (∀ w, evalV F w a = evalV F w b) → a = b := fun a b hab =>
    Subtype.ext (funext hab)
  refine hext _ _ fun v => ?_
  by_contra hne
  rw [map_zero] at hne
  obtain ⟨y, hy⟩ := hv v
  have same : ∀ t, evalV F v (singleV F v t) = t := fun t => RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v t
  have diff : ∀ t w, w ≠ v → evalV F w (singleV F v t) = 0 := fun t w hw => RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) t hw
  refine hy ?_
  rw [psiV, ← hall (singleV F v ((evalV F v l)⁻¹ * y))]
  congr 2
  refine hext _ _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [map_mul, same, same, mul_inv_cancel_left₀ hne]
  · rw [map_mul, diff _ _ hw, diff _ _ hw, mul_zero]

theorem adele_rat {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (hv : ∀ v, ∃ y, psiV F ψ v y ≠ 1)
    (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ))
    (hinf : ∀ x, psiInf F ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x))) (a : AF F)
    (h : ∀ c : F, ψ (a * algebraMap F _ c) = 1) : ∃ d : F, a = algebraMap F _ d := by
  have hsub : ∀ (b : AF F) (x : F), (∀ c : F, ψ (b * algebraMap F _ c) = 1) →
      ∀ c : F, ψ ((b - algebraMap F _ x) * algebraMap F _ c) = 1 := fun b x hb c => by
    rw [sub_mul, ← map_mul, AddChar.map_sub_eq_div, hb, hψ.2.2.1, div_one]
  obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 (sndA F a)
  have h1 := hsub a x h
  have hβ' : sndA F (a - algebraMap F _ x) = β := by
    rw [map_sub, AlgHom.commutes, hx, one_smul, add_sub_cancel_left]
  obtain ⟨d, hd⟩ := inf_rat L hL hT (fstA F (a - algebraMap F _ x)) fun c => by
    have h2 : ψ (pairA F 0 (β * algebraMap F _ (c : F))) = 1 := by
      refine GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 c (fun r => ?_) β hβ
      have h3 := GlobalTheory.StdAdelicChar.ratChar_integer F (r * c)
      rw [GlobalTheory.StdRat.char_fin_rat ψ hψ, hinf, hT, map_neg, ← h3, GlobalTheory.StdAdelicChar.ratChar]
      congr 1
      push_cast
      ring
    have e : (a - algebraMap F _ x) * algebraMap F _ (c : F) =
        pairA F (fstA F (a - algebraMap F _ x) * algebraMap F _ (c : F)) 0 +
          pairA F 0 (β * algebraMap F _ (c : F)) := by
      rw [← hβ']
      exact Prod.ext (add_zero _).symm (zero_add _).symm
    have h4 := h1 c
    rw [e, ψ.map_add_eq_mul, h2, mul_one] at h4
    have h5 := (hinf _).symm.trans h4
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h5
    refine ⟨-n, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
    push_cast
    linear_combination -hn
  have h6 := hsub _ d h1
  have h7 : fstA F (a - algebraMap F _ x - algebraMap F _ d) = 0 := by
    rw [map_sub, AlgHom.commutes, hd, sub_self]
  have h8 := fin_eq_zero hψ.1 hv (sndA F (a - algebraMap F _ x - algebraMap F _ d)) fun c => by
    rw [← h6 c]
    congr 1
    refine Prod.ext ?_ rfl
    change 0 = fstA F (a - algebraMap F _ x - algebraMap F _ d) * _
    rw [h7, zero_mul]
  refine ⟨x + d, ?_⟩
  rw [map_add (f := _), ← sub_eq_zero, ← sub_sub]
  exact Prod.ext h7 h8

end Scalar

theorem tensor_rat {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {R : Type} [CommRing R] [Algebra F R] (z : R ⊗[F] E)
    (h : ∀ e : E, ∃ d : F, Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e * z) = algebraMap F R d) :
    ∃ e : E, z = (1 : R) ⊗ₜ[F] e := by
  classical
  let b := Module.finBasis F E
  have key : ∀ z : R ⊗[F] E,
      z = ∑ i, Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] b i * z) ⊗ₜ[F] b.traceDual i := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [mul_add, map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | tmul a e =>
      conv_lhs => rw [← b.traceDual.sum_repr e, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, GlobalTheory.LatVac.trace_tmul, Module.Basis.traceDual_repr_apply,
        Algebra.traceForm_apply, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm, mul_comm e]
  choose d hd using h
  refine ⟨∑ i, d (b i) • b.traceDual i, ?_⟩
  rw [key z, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem trace_mul_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E]
    {R : Type} [CommRing R] [Algebra F R] (z : R ⊗[F] E) (e : E) (c : F) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e * z) * algebraMap F R c =
      Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] (c • e) * z) := by
  rw [mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc, algebraMap_smul, ← TensorProduct.tmul_smul]

theorem sum_single {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {m n : ℕ} (P : Matrix (Fin m) (Fin m) E)
    (Q : Matrix (Fin n) (Fin n) E) (hP : IsUnit P.det) (hQ : IsUnit Q.det) (a₀ : Fin m) (d₀ : Fin n) (e : E)
    (x : Fin n → Fin m → A) :
    ∑ a, ∑ b, ∑ c, ∑ d, ι (P⁻¹ a b) * ι ((P * Matrix.single a₀ d₀ e * Q⁻¹) b c) * ι (Q c d) * x d a =
      ι e * x d₀ a₀ := by
  have h1 : P⁻¹ * (P * Matrix.single a₀ d₀ e * Q⁻¹) * Q = Matrix.single a₀ d₀ e := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ hP]
  generalize P * Matrix.single a₀ d₀ e * Q⁻¹ = M at h1
  have h2 : ∀ a, ∑ b, ∑ c, ∑ d, ι (P⁻¹ a b) * ι (M b c) * ι (Q c d) * x d a =
      ∑ d, ι (Matrix.single a₀ d₀ e a d) * x d a := fun a => by
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm
  simp only [h2]
  rw [Finset.sum_eq_single a₀, Finset.sum_eq_single d₀, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, map_zero, zero_mul]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne ha.symm, map_zero, zero_mul]
  · simp

theorem exists_symplO_eq {D : D7} (S T : HSp D) (x : WO S T) (i : Fin T.rank) (j : Fin S.rank) (e : D.host.E) :
    ∃ γ ∈ ratL T S, symplO S T x γ = Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j) := by
  refine ⟨ratW T S fun c b => star ((S.gram * Matrix.single j i (D.host.xi0⁻¹ * e) * T.gram⁻¹) b c), ⟨_, rfl⟩, ?_⟩
  have h := sum_single (incA D) S.gram T.gram (GlobalTheory.LatVac.gram_det_isUnit S) (GlobalTheory.LatVac.gram_det_isUnit T) j i
    (D.host.xi0⁻¹ * e) x
  have h2 : hO S T x (ratW T S fun c b =>
      star ((S.gram * Matrix.single j i (D.host.xi0⁻¹ * e) * T.gram⁻¹) b c)) =
      incA D (D.host.xi0⁻¹ * e) * x i j := by
    rw [← h, hO]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    exact congrArg (fun t => incA D (S.gram⁻¹ a b) * t * incA D (T.gram c d) * x d a)
      ((GlobalTheory.DualPairCheck.cA_incA _).trans (congrArg (incA D) (star_star _)))
  rw [symplO, h2, ← mul_assoc, ← RingHom.map_mul, mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

theorem ratL_annihilator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x : WO S T), (∀ γ ∈ ratL T S, ψ (symplO S T x γ) = 1) ↔ x ∈ ratL T S := by
  intro D ψ hψ S T x
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  constructor
  · intro h
    obtain ⟨θ, hθ⟩ := hψ.2.1
    let L : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))) fun a b => by
      simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
    have hrat := adele_rat hψ.1 (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) L
      (continuous_finsetSum _ fun ρ _ => (hθ ρ).2)
      (fun x => by
        show ∑ ρ, θ ρ (algebraMap D.host.F (Ainf D.host.F) x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace])
      (fun y => by
        rw [hψ.2.2 θ hθ]
        congr 1
        change _ = -(_ * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E)))
        push_cast
        ring)
    have hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
      tensor_rat (x i j) fun e => hrat _ fun c => by
        obtain ⟨γ, hγ, hγe⟩ := exists_symplO_eq S T x i j (c • e)
        exact (congrArg ψ ((trace_mul_algebraMap (x i j) e c).trans hγe.symm)).trans (h γ hγ)
    choose M hM using hent
    exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩
  · rintro ⟨γ, rfl⟩ _ ⟨γ', rfl⟩
    obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D S T γ γ'
    exact (congrArg ψ ha).trans (hψ.1.2.2.1 a)

end GlobalTheory.RatAnnih

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaEquivariantPairBoundedFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem exists_l2_lift {H : Type} [AddCommGroup H] [Module ℂ H] (D : Submodule ℂ H) {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (a : H →ₗ[ℂ] (X → ℂ))
    (ha : ∀ w ∈ D, Continuous (a w) ∧ ∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) :
    ∃ A : H →ₗ[ℂ] Lp ℂ 2 ν, ∀ w ∈ D, (A w : X → ℂ) =ᵐ[ν] a w := by
  classical
  have hm : ∀ w : D, MemLp (a w) 2 ν := fun w => by
    obtain ⟨hc, C, hC⟩ := ha w w.2
    exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  let f : D →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun w => (hm w).toLp (a w)
      map_add' := fun w w' => by
        refine Lp.ext ?_
        filter_upwards [(hm (w + w')).coeFn_toLp, (hm w).coeFn_toLp, (hm w').coeFn_toLp,
          Lp.coeFn_add ((hm w).toLp (a w)) ((hm w').toLp (a w'))] with x h1 h2 h3 h4
        rw [h4, Pi.add_apply, h1, h2, h3, Submodule.coe_add, map_add (f := _), Pi.add_apply]
      map_smul' := fun c w => by
        refine Lp.ext ?_
        filter_upwards [(hm (c • w)).coeFn_toLp, (hm w).coeFn_toLp,
          Lp.coeFn_smul c ((hm w).toLp (a w))] with x h1 h2 h3
        rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2, Submodule.coe_smul, map_smul, Pi.smul_apply] }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨g, fun w hw => ?_⟩
  have hgw : g w = f ⟨w, hw⟩ := by rw [← hg]; rfl
  rw [hgw]
  exact (hm ⟨w, hw⟩).coeFn_toLp

theorem l2_inner_of_ae {X : Type} [MeasurableSpace X] {ν : Measure X} {f g : Lp ℂ 2 ν} {u v : X → ℂ}
    (hf : (f : X → ℂ) =ᵐ[ν] u) (hg : (g : X → ℂ) =ᵐ[ν] v) : ⟪f, g⟫_ℂ = ∫ x, star (u x) * v x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x hx hy
  rw [hx, hy, RCLike.inner_apply, mul_comm, starRingEnd_apply]

private lemma jm_sq_lemma {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

private lemma jm_herm_lemma_2 {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : ε i <;> simp [h]

private lemma jm_conjTranspose_jm_mem_and_inverse {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε ∈ UJset ε ∧ (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 ∧
      g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have jj : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, jm_sq_lemma, Matrix.one_mul]
  have hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    calc (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, jm_sq_lemma]
  have hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp hl
  refine ⟨?_, hl, hr⟩
  have hr' : g * (Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε)) = 1 := by simpa only [Matrix.mul_assoc] using hr
  show (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε
  simp only [Matrix.conjTranspose_mul, jm_herm_lemma_2, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, jj]
  rw [hr', Matrix.mul_one]

theorem schurLemma_equivariant_pair_boundedFunctions : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a a' : H →ₗ[ℂ] (X → ℂ)), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), Continuous (a' w) ∧ (∃ C : ℝ, ∀ x, ‖a' w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a' (σ (umat g) w) x = a' w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a')) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a (σ g w) x ∂ν = ∫ x, star (a u x) * a w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a' (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a' u x) * a' w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a u x) * a' w x ∂ν) → ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), ∀ w' ∈ smSub G (trRep σ P), ∫ x, star (a w x) * a' w' x ∂ν = c * ⟪w, w'⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP hG hσ hirr X _ _ _ _ ν _ act hact a a' ha hsa ha' hsa' hI hI' hIx
  obtain ⟨A, hA⟩ := exists_l2_lift (smSub G (trRep σ P)) ν a (fun w hw => ⟨(ha w hw).1, (ha w hw).2.1⟩)
  obtain ⟨A', hA'⟩ := exists_l2_lift (smSub G (trRep σ P)) ν a' (fun w hw => ⟨(ha' w hw).1, (ha' w hw).2.1⟩)
  have hmem : ∀ g ∈ UJset ε, ∀ w ∈ smSub G (trRep σ P), σ g w ∈ smSub G (trRep σ P) :=
    fun g hg w hw => sigma_mem hP hG hσ hw hg
  have hAinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A (σ g u), A (σ g w)⟫_ℂ = ⟪A u, A w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA w hw)]
    exact hI g hg u hu w hw
  have hA'inv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A' (σ g u), A' (σ g w)⟫_ℂ = ⟪A' u, A' w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA' _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA' u hu) (hA' w hw)]
    exact hI' g hg u hu w hw
  have hxinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A (σ g u), A' (σ g w)⟫_ℂ = ⟪A u, A' w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA' w hw)]
    exact hIx g hg u hu w hw
  have hcl := closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A hAinv
    (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
    (_root_.GlobalTheory.SmVec.continuous_toL2_gard n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
    (_root_.GlobalTheory.SmVec.inner_l2_gard n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
  have hcl' := closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A' hA'inv
    (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
    (_root_.GlobalTheory.SmVec.continuous_toL2_gard n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
    (_root_.GlobalTheory.SmVec.inner_l2_gard n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
  have hnorm : ∀ B : H →ₗ[ℂ] Lp ℂ 2 ν, (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪B (σ g u), B (σ g w)⟫_ℂ = ⟪B u, B w⟫_ℂ) →
      ∀ i : UJset ε, ∀ w ∈ smSub G (trRep σ P), ‖B (σ i.1 w)‖ = ‖B w‖ := by
    intro B hB i w hw
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (B w), hB i.1 i.2 w hw w hw]
  have hrep := hσ.1
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.ClosableSchur.inner_eq_pair (UJset ε) H (Lp ℂ 2 ν) (fun i => σ i.1) (smSub G (trRep σ P))
    (fun i v => hσ.2.1 i.1 i.2 v)
    (fun i => by
      obtain ⟨hj, hl, hr⟩ := jm_conjTranspose_jm_mem_and_inverse i.2
      refine ⟨⟨_, hj⟩, fun v => ?_, fun v => ?_⟩
      · show σ _ (σ i.1 v) = v
        rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hj _ i.2, hl, hrep.1,
          ContinuousLinearMap.one_apply]
      · show σ i.1 (σ _ v) = v
        rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ i.2 _ hj, hr, hrep.1,
          ContinuousLinearMap.one_apply])
    (fun S hS hS' => hirr S hS (fun g hg v hv => hS' ⟨g, hg⟩ v hv))
    (fun i v hv => hmem i.1 i.2 v hv)
    A A' (hnorm A hAinv) (hnorm A' hA'inv) (fun i w hw => hxinv i.1 i.2 w hw w hw) hcl hcl'
  exact ⟨c, fun w hw w' hw' => by rw [← l2_inner_of_ae (hA w hw) (hA' w' hw')]; exact hc w hw w' hw'⟩

end GlobalTheory.SmVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeedAtReadingKeeping
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeedChoices


set_option maxHeartbeats 1000000 in
theorem seed_at_reading_keeping : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face3 D A3) (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (ψ : AddChar (AF D.host.F) ℂ) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)), L.Is A3.A.μ0 → Seed.TupL A3 L mu twPl → Seed.RecL A3 L eG → Seed.LevelsL A3 L eG F.lv2 → Seed.ModY D → Seed.ModWAt D.what₂.embLL MW → Seed.VPos D → IsStdChar D ψ (-1) → ∀ Qb : ∀ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)), (∀ t, A3.A.fam.amb.FR t → Bridge.Gf D.sp.X' → cX.W) → (∀ i t, A3.A.fam.amb.FL i t → Bridge.Gf (Vc D i) → (cV i).W) → Prop, (∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m), ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 L cX cV pl) (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL A3 L eG cX cV pl Sb B plI SF ∧ Qb cX cV (fun t φ => B.jR t φ) fun i t φ => B.jL i t φ) → ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.ψ = ψ ∧ R.MW = MW ∧ HEq R.eG eG ∧ R.mu = mu ∧ R.twPl = twPl ∧ Seed.PrIso R.MX R.cX R.prX ∧ R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces ∧ Qb R.cX R.cV (fun t φ => R.B.jR t φ) fun i t φ => R.B.jL i t φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ F L eG mu twPl ψ MW hL hmu hrec hlev hY hMW hV hψ Qb hB
  obtain ⟨θ, hθ⟩ := Formalism.IndefR.Eqv.infFamExists_holds D
  obtain ⟨hMY, ⟨MX⟩⟩ := hY
  let MY := fun j => (hMY j).some
  obtain ⟨cX, cV, pl, Sb, B, plI, SF, prX, hcX, hcV, hpr, hPr, hb, hQ⟩ := hB θ hθ MX
  obtain ⟨gramR, c0R, c0L, htie⟩ := hb.tie
  have hMW' : Seed.ModWAt (D := D) (sg0 D A3.A) MW := by
    rw [show sg0 D A3.A = D.what₂.embLL from sgAt_mk _ htie.v0]; exact hMW
  let R : RealDat D A3.A Ks :=
    { toLevCh := L
      hv0 := htie.v0
      eG := eG
      pl := pl
      Sb := Sb
      θ := θ
      ψ := ψ
      MY := MY
      MX := MX
      MW := MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => Seed.hZ _
      HV := fun _ _ => Seed.hZ _
      HE := Seed.hZ _
      HW := fun _ _ => Seed.hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := mu
      twPl := twPl
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
  refine ⟨{ toRealDat := R, plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }, rfl, rfl, rfl, HEq.rfl, rfl, rfl,
    hPr, ?_, ?_, ?_, hb.sb, hQ⟩
  · have hsub : L.Pg ⊆ Sb := by rw [hb.sb]
    exact ⟨hL, hb.red_R, hb.red_L, hlev, hrec, ⟨⟨gramR, c0R, c0L, htie⟩, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, hθ, hV, hcX, hcV, hpr, hMW', hψ⟩
  · exact ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩
  · exact ⟨hmu.1, hmu.2.1, hmu.2.2.1, hmu.2.2.2.1, hmu.2.2.2.2⟩

end GlobalTheory.SeedChoices
end

