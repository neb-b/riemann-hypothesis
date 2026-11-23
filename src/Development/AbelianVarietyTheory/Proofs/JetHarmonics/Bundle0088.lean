module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExistsAndVectorEqSmulTranslate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriTensorDecomposition
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersMemNormalFormProductSpan
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem hatExp_exists_bound (P : M.Par) :
    ∃ C : ℝ, ∀ t : ℝ, C ≤ t → ∀ ρ : M.Ty P, M.xC P ρ (t : ℂ) ≠ 0 := by
  obtain ⟨C, hC⟩ := (Set.toFinite
    ((fun x : M.Ty P × ℕ => -M.rho P x.1 x.2) ''
      ((Finset.univ ×ˢ Finset.Icc 1 (P.k - 1) : Finset (M.Ty P × ℕ)) : Set (M.Ty P × ℕ)))).bddAbove
  refine ⟨C + 1, fun t ht ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have h1 : -M.rho P ρ i ≤ C :=
    hC ⟨(ρ, i), Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩), rfl⟩
  have h2 : t + M.rho P ρ i ≠ 0 := (show 0 < t + M.rho P ρ i by linarith).ne'
  exact_mod_cast h2

theorem hatExp_exists_nodes (P : M.Par) (n : ℕ) :
    ∃ y : Fin n → ℝ, Function.Injective y ∧ ∀ i, ∀ ρ : M.Ty P,
      M.xC P ρ (y i : ℂ) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) + 1) ≠ 0 := by
  obtain ⟨C, hC⟩ := hatExp_exists_bound P
  refine ⟨fun i => C + 1 + (i : ℕ), fun i j h => ?_, fun i ρ => ?_⟩
  · have h' : ((i : ℕ) : ℝ) = (j : ℕ) := by simpa using h
    exact Fin.ext (by exact_mod_cast h')
  · have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨hC _ (by linarith) ρ, ?_, ?_⟩
    · have := hC (C + 1 + (i : ℕ) - 1) (by linarith) ρ
      rwa [Complex.ofReal_sub, Complex.ofReal_one] at this
    · have := hC (C + 1 + (i : ℕ) + 1) (by linarith) ρ
      rwa [Complex.ofReal_add _ 1, Complex.ofReal_one] at this

theorem hats_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  intro P A _ _ _ _ d hd T a hT
  have hle : nfSpan d (basics d) 0 0 1 ≤ nfSpan d T 0 a 1 := by
    unfold nfSpan
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hH, hHT, rfl⟩
    obtain ⟨h, rfl⟩ := List.length_eq_one_iff.1 hH
    have h1 := ((_root_.GlobalTheory.HatNF.SpanMul.span_mul P A d hd T).1 0 a 1 h (hT h (hHT h (List.mem_singleton_self h)))).1 b hb
    simpa [nfSpan] using h1
  obtain ⟨y, hy, hreg⟩ := hatExp_exists_nodes P (P.r + 2)
  have hyc : Function.Injective fun i => (y i : ℂ) := fun i j h => hy (Complex.ofReal_injective h)
  have hyn : Function.Injective fun i => -(y i : ℂ) := fun i j h => hyc (neg_injective h)
  have key : ∀ (Z : ℂ → A) (X : ℕ → A) (ν : Fin (P.r + 2) → ℂ), Function.Injective ν →
      (∀ s : ℂ, Z s = ∑ j ∈ Finset.range (P.r + 2), s ^ j • X j) →
      (∀ i, Z (ν i) ∈ nfSpan d T 0 a 1) → ∀ s, Z s ∈ nfSpan d T 0 a 1 := by
    intro Z X ν hν hZ hi s
    refine (Submodule.span_le.2 ?_) ((GlobalTheory.T.mem_span_values_of_vector_polynomial A (P.r + 2) Z X ν hν hZ).2 s)
    rintro _ ⟨i, rfl⟩
    exact hi i
  obtain ⟨Xa, Xr, hXa, hXr, -⟩ := _root_.GlobalTheory.HatTaylorPlus.taylor_plus A P.r d.L 0
  obtain ⟨Va, Vr, hVa, hVr, -⟩ := _root_.GlobalTheory.HatNF.TaylorMinus.taylor_minus A P.r d.L 0
  rintro X (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) | ⟨s, rfl⟩)
  · have := key (fun s => d.L.Ahat (0 + s)) Xa _ hyc hXa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inl rfl⟩) s
    simpa using this
  · have := key (fun s => d.L.R0 (0 + s)) Xr _ hyc hXr
      (fun i => by simpa using hle (_root_.GlobalTheory.HatNF.r0_mem_nfSpan_basics P A d hd (y i) (hreg i)).1) s
    simpa using this
  · have := key (fun s => d.L.Ahatv (0 - s)) Va _ hyn hVa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inr (Or.inl rfl)⟩) (-s)
    simpa using this
  · have := key (fun s => d.L.R0v (0 - s)) Vr _ hyn hVr
      (fun i => by simpa using hle (_root_.GlobalTheory.HatNF.r0_mem_nfSpan_basics P A d hd (y i) (hreg i)).2) (-s)
    simpa using this

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermitianDatumDirectPower
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open scoped TensorProduct

namespace GlobalTheory

noncomputable section

def diagEnd {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) : U →ₗ[ℝ] U :=
  e.symm.toLinearMap ∘ₗ (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) ∘ₗ e.toLinearMap

theorem diagEnd_apply {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) (x : U) (i : Fin n) : e (diagEnd e f x) i = f (e x i) := by
  simp [diagEnd]

theorem diagEnd_comp {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f g : V →ₗ[ℝ] V) : diagEnd e f ∘ₗ diagEnd e g = diagEnd e (f ∘ₗ g) := by
  ext x
  apply e.injective
  funext i
  simp [diagEnd_apply]

theorem trace_diagEnd {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] {n : ℕ} (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ U (diagEnd e f) = n * LinearMap.trace ℝ V f := by
  have h1 : diagEnd e f = e.symm.conj (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) := by
    ext x; simp [diagEnd, LinearEquiv.conj_apply]
  have h2 : (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i : (Fin n → V) →ₗ[ℝ] (Fin n → V)) =
      ∑ i, LinearMap.single ℝ (fun _ : Fin n => V) i ∘ₗ (f ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext; intro x
    funext j
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, LinearMap.trace_conj', h2, map_sum]
  have h3 : ∀ i : Fin n, LinearMap.trace ℝ _ (LinearMap.single ℝ (fun _ : Fin n => V) i ∘ₗ (f ∘ₗ LinearMap.proj i)) =
      LinearMap.trace ℝ V f := by
    intro i
    rw [LinearMap.trace_comp_comm']
    congr 1
    ext x; simp
  simp [h3]

def powForm {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → L) :=
  ∑ i, B.compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

theorem powForm_apply {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) (x y : Fin n → L) :
    powForm B n x y = ∑ i, B (x i) (y i) := by
  simp [powForm, LinearMap.sum_apply]

theorem powForm_single {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) (x : Fin n → L)
    (i : Fin n) (y : L) : powForm B n x (Pi.single i y) = B (x i) y := by
  rw [powForm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

theorem powForm_bijective {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (hB : Function.Bijective B)
    (n : ℕ) : Function.Bijective (powForm B n) := by
  constructor
  · intro x y h
    funext i
    apply hB.1
    ext z
    rw [← powForm_single, ← powForm_single, h]
  · intro φ
    choose x hx using fun i : Fin n => hB.2 (φ ∘ₗ LinearMap.single ℤ (fun _ : Fin n => L) i)
    refine ⟨x, ?_⟩
    apply LinearMap.pi_ext
    intro i z
    rw [powForm_single, hx]
    rfl

theorem powForm_baseChange {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ)
    (x y : ℝ ⊗[ℤ] (Fin n → L)) :
    (powForm B n).baseChange ℝ x y =
      ∑ i, B.baseChange ℝ (TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => L) x i)
        (TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => L) y i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, ha, hb, Finset.sum_add_distrib]
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb, Finset.sum_add_distrib]
    | tmul s v => simp [powForm_apply, Finset.sum_smul, Finset.sum_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def powDatum (D : Datum H) (n : ℕ) : Datum H where
  La := Fin n → D.La
  fin := by haveI := D.fin; infer_instance
  proj := by
    haveI := D.proj
    exact Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := 𝓞 E) (M := fun _ : Fin n => D.La))
  EF := powForm D.EF n
  alt := fun x => by simp [powForm_apply, D.alt]
  unimod := powForm_bijective D.EF D.unimod n
  adj := fun a x y => by simp [powForm_apply, D.adj]
  p := n * D.p
  q := n * D.q
  rank := by
    haveI := D.fin
    haveI := D.proj
    have h1 := (TensorProduct.isBaseChange (𝓞 E) (Fin n → D.La) E).finrank_eq
    have h2 := (TensorProduct.isBaseChange (𝓞 E) D.La E).finrank_eq
    have h3 := (TensorProduct.piRight (𝓞 E) E E (fun _ : Fin n => D.La)).finrank_eq
    rw [← h1, h3, Module.finrank_pi_fintype]
    simp [h2, D.rank, mul_add]
  dom := by
    haveI := D.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    set e := TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => D.La) with he
    refine ⟨diagEnd e J, ?_, ?_, ?_, ?_⟩
    · intro x
      apply e.injective
      funext i
      simp [diagEnd_apply, h1]
    · intro x y
      simp only [powForm_baseChange, ← he, diagEnd_apply, h2]
    · intro x hx
      simp only [powForm_baseChange, ← he, diagEnd_apply]
      have : ∃ i, e x i ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hx (e.injective (by rw [map_zero]; exact funext hc))
      obtain ⟨i, hi⟩ := this
      refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, h3 _ hi⟩
      by_cases hj : e x j = 0
      · simp [hj]
      · exact (h3 _ hj).le
    · intro a A t hA ht
      let A0 : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
        ((DistribSMul.toAddMonoidHom D.La a).toIntLinearMap).baseChange ℝ
      obtain ⟨k1, k2, k3⟩ := h4 a A0 _ (fun x => by simp [A0]) rfl
      have hAA : A = diagEnd e A0 := by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
        | tmul r u =>
          have : r ⊗ₜ[ℤ] u = r • ((1 : ℝ) ⊗ₜ[ℤ] u) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul, map_smul, hA]
          congr 1
          apply e.injective
          funext i
          simp [diagEnd_apply, he, A0]
      have ht' : t = n * ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E))) := by
        rw [ht, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        push_cast; ring
      rw [hAA, diagEnd_comp, diagEnd_comp, trace_diagEnd, trace_diagEnd, k1, ← k1, k2, k3, ht']
      refine ⟨rfl, ?_, ?_⟩
      · rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
      · rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im]; ring

theorem exists_datum_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ),
    ∃ (Dw' : Datum H) (e : Dw'.La ≃ₗ[𝓞 E] (Fin n → Dw.La)),
      (∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i)) ∧ Dw'.p = n * Dw.p ∧ Dw'.q = n * Dw.q :=
  fun E _ _ _ _ Dw n => ⟨powDatum Dw n, LinearEquiv.refl (𝓞 E) (Fin n → Dw.La),
    fun x y => powForm_apply Dw.EF n x y, rfl, rfl⟩

end
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]


omit [FiniteDimensional ℂ Wp] in
theorem hsInner_self_eq_normSq (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K]
  simp

omit [FiniteDimensional ℂ Wp] in
theorem hsInner_zero_zero : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
  simp [P.Topx1.hsInner_eq]

theorem levelForm_top_diag (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (a : C.LPt) :
    p.RR H (P.r + 1) w a a = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w a a := by
  by_cases hg : D.IsLocPt a (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r a
  · unfold KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hg.1, hg.1⟩, dite_eq_right (by omega), if_pos rfl]
    split_ifs with hw
    · subst hw
      exact (Formalism.FourierDecayAlt.P.top_of_empty Formalism.FourierDecayAlt.P.vector_valued_types Wp Wq P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H a a p.hP p.hF
        hg.1 hg.1 hg.2 hg.2).symm
    · rfl
  · have hV : ∀ F, D.vecV p.T.base p.ν' p.m₀ F a = 0 := fun F => by
      unfold D.vecV
      rw [dite_eq_right hg]
    have ht : Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w a a = 0 := by
      simp only [Top.topOf, hV, ContinuousLinearMap.comp_zero, hsInner_zero_zero, mul_zero,
        Finset.sum_const_zero]
    rw [ht]
    unfold KB.Pl.RR D.RRplace
    split_ifs with h1 h2 h3 h4
    · omega
    · rw [hV, hsInner_zero_zero]
    · exact ht
    · rfl
    · rfl

end

theorem Ew_eq_norm_tv_sq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = ‖tv p H w c‖ ^ 2 := by
  intro Wp Wq _ _ _ _ _ _ P p H w c
  have h1 : TBB.normC (fun _ => 1) w = 1 := by simp [TBB.normC]
  unfold TBB.Ew TBB.NP
  rw [levelForm_top_diag, h1, div_one, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  unfold Top.topOf
  simp only [hsInner_self_eq_normSq, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp only [tv, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, TBB.TTp, KB.Pl.V]
  ring

end GlobalTheory.TopVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTypeOfIrreducibleStable
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem isType_of_irreducible_stable : ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (Y →L[ℂ] Y)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (S : Submodule ℂ Y) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → Stab (EB π B) S → S ≠ ⊥ → (∀ S' : Submodule ℂ Y, S' ≤ S → Stab (EB π B) S' → S' = ⊥ ∨ S' = S) → (∀ (w : ℂ), ∀ y ∈ S, qdet (EB π B) w y = (∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • y) → ∃ πS : Mx k r → (S →L[ℂ] S), IsType k r z πS u ∧ ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
  intro Y _ _ _ k r z π B S u hz hT hπ hn hB hS hne hirr hcap
  have hst : ∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S :=
    Formalism.FourierDecayAlt.P.lie_stabilizer Y k r z π B hz hT hπ hB S hS
  have hfr0 : ∀ {m : ℕ} (C : Fin m → (Fin (2 * r + k + 1) → ℂ)), IsFrameOf k r [z] C → IsFrameOf k r [z, 0] C := by
    intro m C hC
    refine ⟨hC.1, hC.2.1, fun a v hv => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hC.2.2 a _ (by simp)
    · simp [herm]
  let πS : Mx k r → (S →L[ℂ] S) := fun h => (S.orthogonalProjection).comp ((π h).comp S.subtypeL)
  have hcoe : ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
    intro h hh y
    have := Submodule.orthogonalProjection_mem_subspace_eq_self (K := S) ⟨π h y, hst h hh y y.2⟩
    exact congrArg Subtype.val this
  have hrep : IsRepW k r z πS := by
    refine ⟨⟨?_, fun a _ b hb => ?_⟩, ?_⟩
    · ext y
      simp [πS, hπ.1.1]
    · ext y
      have h1 := hcoe b hb y
      simp only [πS, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at h1 ⊢
      rw [h1, hπ.1.2 a ‹_› b hb]
      rfl
    · exact continuousOn_const.clm_comp (hπ.2.clm_comp continuousOn_const)
  refine ⟨πS, ⟨Submodule.nontrivial_iff_ne_bot.2 hne, hrep.1, hrep.2, ?_, ?_, ?_⟩, hcoe⟩
  · intro h hh v
    rw [Submodule.coe_norm, Submodule.coe_norm, hcoe h hh, hn h hh]
  · intro S'' hS''
    have hstab : Stab (EB π B) (S''.map S.subtype) := by
      refine Formalism.FourierDecayAlt.P.stabilizer_lie_algebra Y k r k z 0 π B hπ (hfr0 B hB) _ ?_
      rintro h hh - _ ⟨y, hy, rfl⟩
      exact ⟨πS h y, hS'' h hh y hy, hcoe h hh y⟩
    rcases hirr _ (Submodule.map_subtype_le S S'') hstab with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_subtype_top])
  · intro B' hB' w v
    rw [(Formalism.FourierDecayAlt.P.frame_general_linear S k r k z πS B' hrep hB').2 w v]
    apply Subtype.ext
    have h1 := GlobalTheory.intertwiner_EB_of_stabiliser S Y k r k z 0 πS π S.subtypeL B' hrep hπ (hfr0 B' hB') (fun h hh _ v => hcoe h hh v)
    have h2 := GlobalTheory.qminor_intertwine Y S k k (EB π B') (EB πS B') S.subtype h1 id id w v
    have h3 := GlobalTheory.capelli_det_frame_indep Y k r z π B B' hz hT hπ hB hB' w
    refine h2.trans ?_
    have h4 := hcap w v v.2
    rw [h3] at h4
    exact h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointApplyOfNormPreserving
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_apply_of_norm_preserving {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (P : V →L[ℂ] V) (hP : ∀ v, ‖P v‖ = ‖v‖) (v : V) :
    ‖ContinuousLinearMap.adjoint P v‖ = ‖v‖ := by
  let L : V →ₗᵢ[ℂ] V := ⟨(P : V →ₗ[ℂ] V), hP⟩
  have hsurj : Function.Surjective (P : V →ₗ[ℂ] V) :=
    LinearMap.surjective_of_injective (f := (P : V →ₗ[ℂ] V)) L.injective
  obtain ⟨u, rfl⟩ := hsurj v
  have h1 : ContinuousLinearMap.adjoint P (P u) = u := by
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact L.inner_map_map u w
  change ‖ContinuousLinearMap.adjoint P (P u)‖ = ‖P u‖
  rw [h1, hP]

theorem norm_adjoint_of_intertwine {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (P : V →L[ℂ] V) (Q : U →L[ℂ] U) (A A' : U →L[ℂ] V) (hQ : ∀ v, ‖Q v‖ = ‖v‖)
    (h : A'.comp Q = P.comp A) (v : V) :
    ‖ContinuousLinearMap.adjoint A' v‖ = ‖ContinuousLinearMap.adjoint A (ContinuousLinearMap.adjoint P v)‖ := by
  rw [← norm_adjoint_apply_of_norm_preserving Q hQ]
  have h1 := congrArg (fun T : U →L[ℂ] V => ContinuousLinearMap.adjoint T v) h
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] at h1
  rw [h1]

theorem norm_adjoint_real_pow_smul {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (A : U →L[ℂ] V) (t : ℝ) (d : ℕ) (v : V) :
    ‖ContinuousLinearMap.adjoint (((t : ℂ) ^ d) • A) v‖ ^ 2 =
      (t ^ 2) ^ d * ‖ContinuousLinearMap.adjoint A v‖ ^ 2 := by
  rw [LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply, norm_smul, mul_pow]
  congr 1
  rw [RCLike.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, mul_comm, pow_mul, sq_abs]

theorem lower_bound_spreads :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (πp : Mx (n + 1) r → (Vp →L[ℂ] Vp)) (πm : Mx (n + 1) r → (Vm →L[ℂ] Vm)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (Ap : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vm →L[ℂ] V)) (n₀ : ℕ) (b : ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πp h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πm h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → GlobalTheory.WigSh.WigMap (n + 1) r z πp π n₀ Ap → GlobalTheory.WigSh.WigMap (n + 1) r z πm π n₀ Am → (∀ v : V, ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap (B (Fin.last n))) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am (B (Fin.last n))) v‖ ^ 2)) → ∀ ω, inWb (n + 1) r ω → herm (Hpk (n + 1) r) ω z = 0 → ∀ v : V, (herm (Hpk (n + 1) r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ n r z π πp πm B Ap Am n₀ b hz hT hπ hπp hπm hB hAp hAm hlow ω hω hωz v
  obtain ⟨t, h, hh, -, hre, rfl⟩ :=
    (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).2 B hB ω hω hωz
  rw [hre, hAp.2.2.1, hAm.2.2.1, norm_adjoint_real_pow_smul, norm_adjoint_real_pow_smul,
    norm_adjoint_of_intertwine (π h) (πp h) _ _ (hπp h hh) (hAp.2.1 h hh _),
    norm_adjoint_of_intertwine (π h) (πm h) _ _ (hπm h hh) (hAm.2.1 h hh _)]
  have h1 := hlow (ContinuousLinearMap.adjoint (π h) v)
  rw [norm_adjoint_apply_of_norm_preserving (π h) (hπ h hh)] at h1
  have h2 : (0 : ℝ) ≤ (t ^ 2) ^ n₀ := by positivity
  calc _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriTensorDecompositionStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pieri_tensor_decomposition : Hyps → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → ∀ ν, (∀ l, n1 ν + l ≤ q0 → ∃ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep) ∧ (n1 ν + 1 ≤ q0 → ∃ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep) := by
  first | exact @GlobalTheory.TensExists.tens_exists | exact GlobalTheory.TensExists.tens_exists | (intros; apply GlobalTheory.TensExists.tens_exists <;> assumption)
end

