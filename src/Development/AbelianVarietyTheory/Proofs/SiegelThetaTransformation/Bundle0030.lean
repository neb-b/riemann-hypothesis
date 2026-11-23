module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierExpansionHolomorphicTube
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEventuallyCongr
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory

namespace GlobalTheory.IsoTower

theorem finite_quot_nsmul (M : Type) [AddCommGroup M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    Finite (M ⧸ (nsmulAddMonoidHom n : M →+ M).range) := by
  have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨y, rfl⟩

theorem exists_eventually_congr {L M : Type} [AddCommGroup L] [AddCommGroup M]
    [Module.Finite ℤ L] [Module.Finite ℤ M] (U : Ultrafilter ℕ) (g : ℕ → L →+ M) {n : ℕ} (hn : 0 < n)
    (P : ℕ → Prop) (hP : ∀ᶠ j in U, P j) :
    ∃ i, P i ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e := by
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 (inferInstance : Module.Finite ℤ L))
  have := hSf.to_subtype
  have := finite_quot_nsmul M hn
  let φ : ℕ → S → M ⧸ (nsmulAddMonoidHom n : M →+ M).range := fun j s => QuotientAddGroup.mk (g j s)
  obtain ⟨v, hv⟩ := Ultrafilter.eq_pure_of_finite (U.map φ)
  have hv' : ∀ᶠ j in U, φ j = v := by
    have : {v} ∈ U.map φ := by
      rw [hv]
      exact rfl
    exact this
  obtain ⟨i, hi, hPi⟩ := (hv'.and hP).exists
  refine ⟨i, hPi, hv'.mono fun j hj a => ?_⟩
  have h := AddMonoidHom.eq_of_eqOn_dense hS
    (f := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g i))
    (g := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g j))
    (fun s hs => congrFun (hi.trans hj.symm) ⟨s, hs⟩)
  obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 (DFunLike.congr_fun h a)
  refine ⟨e, ?_⟩
  have he' : n • e = -g i a + g j a := he
  rw [he']
  abel

end GlobalTheory.IsoTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierEntire
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.LevelTheta

theorem exists_fourier_entire {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z, ∀ m : ι → ℤ, f (z + fun i => (m i : ℂ)) = f z) :
    ∃ a : (ι → ℤ) → ℂ,
      (∀ z, HasSum (fun ν : ι → ℤ => a ν * cexp (2 * π * I * ∑ i, (ν i : ℂ) * z i)) (f z)) ∧
      ∀ (w : ι → ℂ) (ν : ι → ℤ), a ν = ∫ x in Set.Icc (0 : ι → ℝ) 1,
        f ((fun i => (x i : ℂ)) + w) *
          cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + w i))) := by
  obtain ⟨a, h1, h2⟩ := exists_fourier_expansion_tube ι Set.univ f isOpen_univ convex_univ
    hf.differentiableOn (fun z _ m => hper z m)
  refine ⟨a, fun z => h1 z trivial, fun w ν => ?_⟩
  have key := Koecher.setIntegral_unitCube_tube (U := Set.univ)
    (f := fun z => f z * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * z i))) isOpen_univ
    isPreconnected_univ (fun _ _ _ => trivial)
    (hf.differentiableOn.mul (Differentiable.differentiableOn (by fun_prop))) (fun z hz i => ?_)
    (Set.mem_univ (fun i => I * (((0 : ι → ℝ) i : ℝ) : ℂ))) (Set.mem_univ w)
  · rw [h2 0 trivial ν]
    refine Eq.trans ?_ key
    exact (setIntegral_congr_set (μ := volume) (Measure.univ_pi_Ico_ae_eq_Icc
      (f := (0 : ι → ℝ)) (g := 1)))
  · have e0 : (Pi.single i 1 : ι → ℂ) = fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℂ) := by
      funext j
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij]
    have e : ∑ j, (ν j : ℂ) * (z + (Pi.single i 1 : ι → ℂ)) j
        = ∑ j, (ν j : ℂ) * z j + ν i := by
      simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
    rw [e, e0, hper z, mul_add, neg_add, Complex.exp_add]
    have : cexp (-(2 * π * I * (ν i : ℂ))) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I (-ν i)]
      congr 1
      push_cast
      ring
    rw [this, mul_one]

theorem quad_add {ι : Type} [Fintype ι] {τ : Matrix ι ι ℂ} (h : τ.IsSymm) (u v : ι → ℂ) :
    (u + v) ⬝ᵥ τ *ᵥ (u + v) = u ⬝ᵥ τ *ᵥ u + 2 * (u ⬝ᵥ τ *ᵥ v) + v ⬝ᵥ τ *ᵥ v := by
  have : v ⬝ᵥ τ *ᵥ u = u ⬝ᵥ τ *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, h.eq, dotProduct_comm]
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, this]
  ring

theorem exists_thS_eq : ∀ (n g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ Siegel (Fin g) → ∀ (N : ℕ), 0 < N → ∀ Θ : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ Θ → (∀ (a : Fin n → Fin g → ℤ) ζ, Θ (fun k i => ζ k i + N * a k i) = Θ ζ) → (∀ (b : Fin n → Fin g → ℤ) ζ, cexp (π * I * ∑ k, ((fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ (fun i => (N * b k i : ℂ)) + 2 * ((fun i => (N * b k i : ℂ)) ⬝ᵥ ζ k))) * Θ (fun k => ζ k + τ *ᵥ fun i => (N * b k i : ℂ)) = Θ ζ) → ∃ φ : TF n g, IsSB φ ∧ ∀ ζ, thS φ τ ζ = Θ ζ := by
  intro n g τ hτ N hN Θ hΘ hp hq
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨a, hs, ha⟩ := exists_fourier_entire (ι := Fin n × Fin g)
    (fun z => Θ fun k i => N * z (k, i)) (hΘ.comp (by fun_prop)) (fun z m => by
      rw [← hp (fun k i => m (k, i)) fun k i => N * z (k, i)]
      congr 1
      funext k i
      simp [mul_add])
  let e : (Fin n × Fin g → ℤ) → Matrix (Fin n) (Fin g) ℚ :=
    fun ν => Matrix.of fun k i => (ν (k, i) : ℚ) / N
  have he : Function.Injective e := by
    intro m m' hmn
    funext ⟨k, i⟩
    have h1 : (m (k, i) : ℚ) / N = (m' (k, i) : ℚ) / N := congrFun (congrFun hmn k) i
    exact_mod_cast (div_left_inj' hNq).1 h1
  let Q : Matrix (Fin n) (Fin g) ℚ → ℂ := fun x => ∑ k, qv (x k) ⬝ᵥ τ *ᵥ qv (x k)
  let φ : TF n g := fun x => Function.extend e a 0 x * cexp (-(π * I * Q x))
  have hφe : ∀ ν, φ (e ν) = a ν * cexp (-(π * I * Q (e ν))) := fun ν => by
    simp only [φ, he.extend_apply]
  have hφ0 : ∀ x, x ∉ Set.range e → φ x = 0 := fun x hx => by
    simp only [φ]
    rw [Function.extend_apply' _ _ _ hx]
    simp
  have hshift : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ),
      e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ)) =
        e (fun p => ν p + N ^ 2 * b p.1 p.2) := by
    intro ν b
    ext k i
    simp only [e, of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  have hlaw : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ),
      φ (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) = φ (e ν) := by
    intro ν b
    have hQ : Q (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) =
        Q (e ν) + 2 * ∑ k, ∑ i, (ν (k, i) : ℂ) * (τ *ᵥ fun j => (b k j : ℂ)) i +
          ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ (fun i => (N * b k i : ℂ)) := by
      simp only [Q, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : qv ((e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) k) =
          qv (e ν k) + fun i => (N * b k i : ℂ) := by
        funext i
        simp [qv]
      rw [h1, quad_add hτ.1]
      congr 2
      have h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ) := by
        funext i; simp
      rw [h2, mulVec_smul, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [qv, e, of_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
    have h := hφe (fun p => ν p + N ^ 2 * b p.1 p.2)
    rw [← hshift] at h
    rw [h, hφe, hQ, ha 0, ha (fun p => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) ν,
      ← integral_mul_const, ← integral_mul_const]
    congr 1
    funext x
    rw [← hq b]
    have h3 : (fun k => (fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) k +
        τ *ᵥ fun i => (N * b k i : ℂ)) =
        fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) +
          fun p : Fin n × Fin g => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) (k, i) := by
      funext k i
      have h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ) := by
        funext i; simp
      rw [h2, mulVec_smul]
      simp [mul_add]
    rw [h3, mul_comm (cexp _) (Θ _)]
    simp only [mul_assoc (Θ _), ← Complex.exp_add]
    congr 2
    have h4 : ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ
        (fun i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) =
        ∑ k, ∑ i, (N : ℂ) ^ 2 * b k i * x (k, i) := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.zero_apply]
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h4]
    simp only [Fintype.sum_prod_type, Pi.zero_apply, add_zero, mul_add, add_mul,
      Finset.sum_add_distrib, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    ring
  refine ⟨φ, ⟨N, hN, fun x hx => ?_, fun x y hy => ?_⟩, fun ζ => ?_⟩
  · obtain ⟨ν, rfl⟩ : x ∈ Set.range e := by
      by_contra h
      exact hx (hφ0 x h)
    intro k i
    have : ((N : ℚ) • e ν) k i = algebraMap ℤ ℚ (ν (k, i)) := by
      simp only [e, of_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]
      field_simp
    rw [this]
    exact isIntegral_algebraMap
  · have : ∀ k i, ∃ m : ℤ, (m : ℚ) = y k i := fun k i => by
      simpa using IsIntegrallyClosed.isIntegral_iff.1 (hy k i)
    choose b hb using this
    obtain rfl : y = Matrix.of fun k i => (b k i : ℚ) := by
      ext k i
      simp [hb]
    by_cases hx : x ∈ Set.range e
    · obtain ⟨ν, rfl⟩ := hx
      exact hlaw ν b
    · rw [hφ0 x hx]
      refine hφ0 _ ?_
      rintro ⟨ν, hν⟩
      refine hx ⟨fun p => ν p + N ^ 2 * (-b) p.1 p.2, ?_⟩
      rw [← hshift, hν]
      ext k i
      simp
  · have h1 := hs fun p => ζ p.1 p.2 / N
    have h2 : (fun k i => (N : ℂ) * (ζ k i / N)) = ζ := by
      funext k i
      field_simp
    simp only [h2] at h1
    refine HasSum.tsum_eq ?_
    refine (he.hasSum_iff fun x hx => by rw [hφ0 x hx, zero_mul]).1 ?_
    convert h1 using 2 with ν
    simp only [Function.comp_apply]
    rw [hφe, mul_assoc, ← Complex.exp_add]
    congr 2
    have h3 : ∑ k, qv (e ν k) ⬝ᵥ ζ k = ∑ p : Fin n × Fin g, (ν p : ℂ) * (ζ p.1 p.2 / N) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [qv, e, of_apply]
      push_cast
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h3]
    simp only [Q]
    ring

end GlobalTheory.Ker.LevelTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFundamentalDomain
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical Topology

namespace GlobalTheory.SW.LatFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in
theorem mapL_mul (γ γ' : GL (Fin r) E) (L : Lt E r) : mapL (γ * γ') L = mapL γ (mapL γ' L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL 1 L = L := by
  ext v
  simp [mapL]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  change (1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

omit [NumberField E] [IsCMField E] in
theorem lact_mul {Ψ : Finset (E →+* ℂ)} (γ' γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ' * γ) x = lact γ' (lact γ x) := by
  first
  | exact @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | (apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame ..)

omit [NumberField E] [IsCMField E] in
theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Continuous (lact γ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop


omit [IsCMField E] in
theorem countable_fg : {L : Lt E r | L.FG}.Countable := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  refine (Set.countable_range fun s : Finset (Fin r → E) =>
    Submodule.span (𝓞 E) (s : Set (Fin r → E))).mono ?_
  rintro L ⟨s, hs⟩
  exact ⟨s, hs⟩


omit [IsCMField E] in
theorem exists_den {L : Lt E r} (hL : L.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ v ∈ L, ∀ a, ∃ c : 𝓞 E, (c : E) = (d : E) * v a := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator ..)

theorem eq_zero_of_small (X : Data E r) (c : 𝓞 E) (h : ∀ τ : X.Ψ, ‖τ.1 (c : E)‖ < 1) : c = 0 := by
  by_contra hc
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hc
  by_cases hs : σ ∈ X.Ψ
  · exact absurd (h ⟨σ, hs⟩) (not_lt.2 hσ)
  · have h1 : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      by_contra h2
      exact hs ((X.cmType σ).2 h2)
    have h3 := h ⟨_, h1⟩
    simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h3
    exact absurd h3 (not_lt.2 hσ)

theorem exists_nhds (X : Data E r) {L : Lt E r} (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ U ∈ 𝓝 x, ∀ γ : GL (Fin r) E, mapL γ L = L → lact γ x ∈ U → γ = 1 := by
  obtain ⟨d, hd0, hd⟩ := exists_den hL
  obtain ⟨s, hs⟩ := hL
  let f : (Fin r → E) → X.Ψ → Fin r → Frame X.Ψ r → ℝ := fun v τ a y =>
    ‖τ.1 (d : E) * ((mat y τ *ᵥ ((mat x τ)⁻¹ *ᵥ fun b => τ.1 (v b))) a - τ.1 (v a))‖
  have hf : ∀ v τ a, Continuous (f v τ a) := fun v τ a => by
    simp only [f, mat, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  have hu : ∀ τ, IsUnit (mat x τ).det := fun τ => (hx τ).1.isUnit
  refine ⟨{y | ∀ v ∈ s, ∀ τ a, f v τ a y < 1}, ?_, fun γ hγ hy => ?_⟩
  · refine (Filter.eventually_all_finset s).2 fun v _ => Filter.eventually_all.2 fun τ =>
      Filter.eventually_all.2 fun a => ?_
    refine (hf v τ a).continuousAt.eventually_lt continuousAt_const ?_
    simp [f, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu τ)]
  · have h1 : ∀ v ∈ s, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
      have hvL : v ∈ L := hs ▸ Submodule.subset_span hv
      have hγv : (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ L := by
        rw [← hγ]
        exact ⟨v, hvL, by simp⟩
      funext a
      obtain ⟨c, hc⟩ := hd _ (L.sub_mem hγv hvL) a
      have hc0 : c = 0 := eq_zero_of_small X c fun τ => by
        have h2 := hy v hv τ a
        have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
        simp only [f, e1, Matrix.mulVec_mulVec, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ (hu τ), Matrix.mul_one] at h2
        rw [hc]
        convert h2 using 2
        simp [Matrix.mulVec, dotProduct]
      rw [hc0] at hc
      have hd1 : (d : E) ≠ 0 := by exact_mod_cast hd0
      have := (mul_eq_zero.1 (hc.symm.trans (by simp))).resolve_left hd1
      exact sub_eq_zero.1 this
    have h2 : ∀ v ∈ L, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem v hv => exact h1 v hv
      | zero => simp
      | add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]
      | smul t v _ hv => rw [Matrix.mulVec_smul, hv]
    have h3 : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v => by
      have hv : v ∈ Submodule.span E (L : Set (Fin r → E)) := hsp ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv => exact h2 v hv
      | zero => simp
      | add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]
      | smul t v _ hv => rw [Matrix.mulVec_smul, hv]
    ext i j
    have := congrFun (h3 (Pi.single j 1)) i
    simpa [Matrix.one_apply, Pi.single_apply] using this

theorem exists_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)), (∀ γ ∈ Δ, IsUn X γ) → (∀ L ∈ 𝓛, L.FG ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤) → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛) → 𝓛.Countable ∧ (∀ (γ γ' : GL (Fin r) E) L, mapL (γ * γ') L = mapL γ (mapL γ' L)) ∧ (∀ L : Lt E r, mapL 1 L = L) ∧ ∃ D : Lt E r → Set (Frame X.Ψ r), (∀ L, MeasurableSet (D L) ∧ D L ⊆ X.dom) ∧ ∀ L ∈ 𝓛, ∀ x ∈ X.dom, ∃! γ : Δ, lact γ x ∈ D (mapL γ L) := by
  intro E _ _ _ r X Δ 𝓛 hun hlat hstab
  have hc : 𝓛.Countable := countable_fg.mono fun L hL => (hlat L hL).1
  refine ⟨hc, mapL_mul, mapL_one, ?_⟩
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  have : Countable (GL (Fin r) E) := Units.val_injective.countable
  have : Countable 𝓛 := hc.to_subtype
  letI : TopologicalSpace 𝓛 := ⊥
  have : DiscreteTopology 𝓛 := ⟨rfl⟩
  letI : MeasurableSpace 𝓛 := ⊤
  have : OpensMeasurableSpace 𝓛 := ⟨le_top⟩
  letI act : MulAction Δ (𝓛 × X.dom) :=
    { smul := fun γ p => (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩)
      one_smul := fun p => Prod.ext (Subtype.ext (mapL_one _)) (Subtype.ext (lact_one _))
      mul_smul := fun γ γ' p =>
        Prod.ext (Subtype.ext (mapL_mul _ _ _)) (Subtype.ext (lact_mul _ _ _)) }
  have hsm : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p =
    (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩) := fun _ _ => rfl
  have : MeasurableConstSMul Δ (𝓛 × X.dom) := ⟨fun γ => by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_from_top (f := fun L : 𝓛 => (⟨mapL γ L, hstab _ γ.2 _ L.2⟩ : 𝓛))).comp
        measurable_fst
    · exact (((continuous_lact (γ : GL (Fin r) E)).measurable.comp
        measurable_subtype_coe).comp measurable_snd).subtype_mk⟩
  have hdisc : ∀ p : 𝓛 × X.dom, ∃ U ∈ 𝓝 p, ∀ γ : Δ, γ • p ∈ U → γ = 1 := fun p => by
    obtain ⟨U, hU, h⟩ := exists_nhds X (hlat _ p.1.2).1 (hlat _ p.1.2).2 p.2.2
    refine ⟨{p.1} ×ˢ (Subtype.val ⁻¹' U), prod_mem_nhds ((isOpen_discrete _).mem_nhds rfl)
      (continuous_subtype_val.continuousAt.preimage_mem_nhds hU), fun γ hγ => ?_⟩
    exact Subtype.ext (h γ (congrArg Subtype.val hγ.1) hγ.2)
  have hfree : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p = p → γ = 1 := fun γ p h => by
    obtain ⟨U, hU, h'⟩ := hdisc p
    exact h' γ (h.symm ▸ mem_of_mem_nhds hU)
  obtain ⟨D, hD, hcov, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := Δ)
    (X := 𝓛 × X.dom)
    (fun g => by
      by_cases hg : g = 1
      · simp [hg]
      · have : {p : 𝓛 × X.dom | g • p = p} = ∅ :=
          Set.eq_empty_of_forall_notMem fun p hp => hg (hfree g p hp)
        simp [this])
    (fun p => by
      obtain ⟨U, hU, h⟩ := hdisc p
      exact ⟨U, hU, fun g hg => by rw [h g hg, one_smul]⟩)
  refine ⟨fun L => {y | ∃ (hL : L ∈ 𝓛) (hy : y ∈ X.dom), ((⟨L, hL⟩, ⟨y, hy⟩) : 𝓛 × X.dom) ∈ D},
    fun L => ⟨?_, fun y hy => hy.2.1⟩, fun L hL x hx => ?_⟩
  · by_cases hL : L ∈ 𝓛
    · have h := (MeasurableEmbedding.subtype_coe
        (FourierCoefficientDomain.isOpen_dom X).measurableSet).measurableSet_image.2
        (measurable_prodMk_left (x := (⟨L, hL⟩ : 𝓛)) hD)
      convert h using 1
      ext y
      exact ⟨fun ⟨_, hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨z, h, e⟩ => e ▸ ⟨hL, z.2, h⟩⟩
    · simp [hL]
  · obtain ⟨g, hg⟩ := hcov (⟨L, hL⟩, ⟨x, hx⟩)
    refine ⟨g, ⟨_, _, hg⟩, fun k hk => ?_⟩
    obtain ⟨_, _, hk⟩ := hk
    have := hu _ hg (k * g⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hk)
    exact mul_inv_eq_one.1 (hfree _ _ this)

end GlobalTheory.SW.LatFrame
end

