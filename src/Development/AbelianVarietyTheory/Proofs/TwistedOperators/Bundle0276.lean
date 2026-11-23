module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalUnitaryScalingWittFrame
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial
open Matrix
open Formalism.UG (cT cT_mul cT_one)
open scoped Classical

noncomputable section

namespace GlobalTheory.TrScale

theorem exists_scale (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) : ∃ g : GF V, (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x) ∧ (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E)⁻¹ • x) ∧ ∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z := by
  let b : Fin (wittIndex V) × Bool → V.V := fun a => if a.2 then Φ.e a.1 else Φ.f a.1
  let σ : D.host.E →+* D.host.E := D.sp.cm.sig
  let d : Fin (wittIndex V) × Bool → D.host.E := fun a =>
    if u a.1 = 0 then 1 else if (u a.1 = 1 ↔ a.2 = true) then 2 else 2⁻¹
  have h2 : (2 : D.host.E) ≠ 0 := two_ne_zero
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have hσd : ∀ i s, σ (d (i, s)) * d (i, !s) = 1 := fun i s => by
    simp only [d]
    split_ifs <;> cases s <;> simp_all [map_inv₀, hσ2, h2]
  let S : Matrix (Fin (wittIndex V) × Bool) (Fin (wittIndex V) × Bool) D.host.E :=
    (1 : Matrix _ _ D.host.E).submatrix id ((Equiv.refl _).prodCongr Equiv.boolNot)
  have fe : ∀ i j, V.hT (Φ.f i) (Φ.e j) = if i = j then 1 else 0 := fun i j => (Φ.ef j i).trans (by simp only [eq_comm])
  have ef : ∀ i j, V.hT (Φ.e i) (Φ.f j) = if i = j then 1 else 0 := fun i j => by
    rw [← V.herm.eq, fe]; by_cases h : i = j <;> simp [h, eq_comm]
  have ee : ∀ i j, V.hT (Φ.e i) (Φ.e j) = 0 := fun i j => Φ.ee j i
  have ff : ∀ i j, V.hT (Φ.f i) (Φ.f j) = 0 := fun i j => Φ.ff j i
  have hB : cT σ (cols V b) * V.gram * cols V b = S := by
    rw [gram_cols]
    ext ⟨i, _ | _⟩ ⟨j, _ | _⟩ <;> simp [b, S, ee, ff, ef, fe, Matrix.one_apply]
  have hSS : S * S = 1 := by
    refine (Matrix.mul_submatrix_one (Equiv.refl _) _ S).trans ?_
    ext ⟨i, s⟩ ⟨j, t⟩
    simp [S, Matrix.one_apply]
  have hS : cT σ S = S := by
    ext ⟨i, _ | _⟩ ⟨j, _ | _⟩ <;> simp [cT, S, Matrix.one_apply, eq_comm, apply_ite σ]
  let P : Matrix (Fin (wittIndex V) × Bool) (Fin (wittIndex V) × Bool) D.host.E := diagonal d
  have hP : cT σ P * S * P = S := by
    have hc : cT σ P = diagonal fun a => σ (d a) := by
      ext a c; by_cases h : a = c <;> simp [cT, P, diagonal_apply, h, eq_comm]
    rw [hc]
    ext ⟨i, s⟩ ⟨j, t⟩
    simp only [P, Matrix.mul_diagonal, Matrix.diagonal_mul, S, submatrix_apply, Matrix.one_apply, id, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, Prod.mk.injEq, Equiv.boolNot_apply]
    by_cases hij : i = j
    · subst hij
      cases s <;> cases t <;> simp only [true_and, and_true, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, and_self, mul_one, mul_zero, zero_mul, and_false, ite_true, ite_false, Prod.mk.injEq]
      all_goals first | exact hσd i _ | exact congrArg _ (hσd i _) | skip
    · simp [hij]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = S * (cT σ (cols V b) * V.gram) := ⟨_, rfl⟩
  have hQB : Q * cols V b = 1 := by rw [hQ, Matrix.mul_assoc, hB, hSS]
  have h1 : cT σ (cols V b) * V.gram = S * Q := by rw [hQ, ← Matrix.mul_assoc S S, hSS, Matrix.one_mul]
  have h2' : V.gram * cols V b = cT σ Q * S := by
    have := congrArg (cT σ) h1
    rwa [cT_mul, cT_mul, AutFunCompare.cT_cT', IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_gram, hS] at this
  have hw := unitary_extension σ h1 h2' hQB hP
  have hi : V.gram⁻¹ * (cT σ (1 + cols V b * (P - 1) * Q) * V.gram) * (1 + cols V b * (P - 1) * Q) = 1 := by
    rw [Matrix.mul_assoc, hw, Matrix.nonsing_inv_mul _ (IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V)]
  let w : GF V := ⟨⟨_, _, mul_eq_one_comm.1 hi, hi⟩, hw⟩
  have act : ∀ {p : Type} (x y : p → V.V), (1 + cols V b * (P - 1) * Q) * cols V x = cols V y →
      ∀ a, GlobalTheory.Cusp.ratAct D.sp.cm V w (x a) = y a := fun x y h a => by
    refine V.frame.repr.injective (DFunLike.coe_injective ?_)
    rw [GlobalTheory.Cusp.ratAct, Matrix.repr_toLin]
    exact funext fun i => congrFun (congrFun h i) a
  have hwb : ∀ a, GlobalTheory.Cusp.ratAct D.sp.cm V w (b a) = d a • b a := act b (fun a => d a • b a) (by
    rw [Matrix.add_mul, Matrix.mul_assoc, hQB, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      add_sub_cancel]
    ext r a; simp [cols, P, Matrix.mul_diagonal, mul_comm])
  refine ⟨w, fun x hx => ?_, fun x hx => ?_, fun z hz1 hz2 => ?_⟩
  · refine (Submodule.span_le (p := LinearMap.eqLocus (GlobalTheory.Cusp.ratAct D.sp.cm V w) ((2 : D.host.E) • LinearMap.id))).2 ?_ hx
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> simp only [Set.mem_setOf_eq] at hi
    · have := hwb (i, true); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
    · have := hwb (i, false); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
  · refine (Submodule.span_le (p := LinearMap.eqLocus (GlobalTheory.Cusp.ratAct D.sp.cm V w) ((2 : D.host.E)⁻¹ • LinearMap.id))).2 ?_ hx
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_eq_iff_eq_neg] at hi
    · have := hwb (i, true); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
    · have := hwb (i, false); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
  · have hz : ∀ a, u a.1 ≠ 0 → V.hT (b a) z = 0 := by
      rintro ⟨i, s⟩ h
      have hm1 : ∀ x, x ∈ Φ.sub u ∨ x ∈ Φ.sub (-u) → V.hT x z = 0 := fun x hx => hx.elim (hz1 x) (hz2 x)
      apply hm1
      rcases (show u i = 1 ∨ u i = -1 by generalize u i = t at h; revert t; decide) with h' | h' <;> cases s <;>
        simp only [b, if_true, if_false, Bool.false_eq_true]
      · exact .inr (by rw [WittFrame.sub]; exact Submodule.subset_span (.inr ⟨i, by simp [h'], rfl⟩))
      · exact .inl (by rw [WittFrame.sub]; exact Submodule.subset_span (.inl ⟨i, h', rfl⟩))
      · exact .inl (by rw [WittFrame.sub]; exact Submodule.subset_span (.inr ⟨i, h', rfl⟩))
      · exact .inr (by rw [WittFrame.sub]; exact Submodule.subset_span (.inl ⟨i, by simp [h'], rfl⟩))
    have hY : Q * cols V (fun _ : Unit => z) = S * of fun a (_ : Unit) => V.hT (b a) z := by
      rw [hQ, Matrix.mul_assoc, gram_cols]
    have hSY : S * of (fun a (_ : Unit) => V.hT (b a) z) = of fun (a : Fin (wittIndex V) × Bool) (_ : Unit) => V.hT (b (a.1, !a.2)) z := by
      simp only [S]; rw [Matrix.one_submatrix_mul]
      ext ⟨i, s⟩ c; rfl
    have hZ : (P - 1) * of (fun (a : Fin (wittIndex V) × Bool) (_ : Unit) => V.hT (b (a.1, !a.2)) z) = 0 := by
      ext ⟨i, s⟩ c
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, show P = diagonal d from rfl, Matrix.diagonal_mul, of_apply,
        Matrix.zero_apply]
      by_cases hu : u i = 0
      · simp [d, hu]
      · rw [hz (i, !s) hu]; simp
    have key : (1 + cols V b * (P - 1) * Q) * cols V (fun _ : Unit => z) = cols V (fun _ : Unit => z) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hY, hSY, hZ, Matrix.mul_zero, add_zero]
    exact act (fun _ : Unit => z) (fun _ => z) key ()

end GlobalTheory.TrScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniqueIntertwiner
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CuspIntertwiner

theorem exists_extend {ι H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (e : ι → H) (f : ι → K)
    (he : Dense (Submodule.span ℂ (Set.range e) : Set H)) (c : ℂ) (h : ∀ i j, ⟪f i, f j⟫_ℂ = c * ⟪e i, e j⟫_ℂ) :
    ∃ A : H →L[ℂ] K, ∀ i, A (e i) = f i := by
  have hd : DenseRange (Finsupp.linearCombination ℂ e) := by
    rw [← Finsupp.range_linearCombination] at he
    exact he
  have hn : ∀ x : ι →₀ ℂ, ‖Finsupp.linearCombination ℂ f x‖ ≤ √‖c‖ * ‖Finsupp.linearCombination ℂ e x‖ := by
    intro x
    have h1 : ⟪Finsupp.linearCombination ℂ f x, Finsupp.linearCombination ℂ f x⟫_ℂ =
        c * ⟪Finsupp.linearCombination ℂ e x, Finsupp.linearCombination ℂ e x⟫_ℂ := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
        inner_smul_right, h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 := congrArg norm h1
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
    simp only [norm_pow, RCLike.norm_ofReal, abs_norm] at h2
    refine le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_)
    rw [h2, mul_pow, Real.sq_sqrt (norm_nonneg _)]
  refine ⟨(Finsupp.linearCombination ℂ f).extendOfNorm (Finsupp.linearCombination ℂ e), fun i => ?_⟩
  have := LinearMap.extendOfNorm_eq hd ⟨_, hn⟩ (Finsupp.single i 1)
  simpa using this

theorem continuous_tens {κ H : Type} [Fintype κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) : Continuous t := by
  refine continuous_iff_continuousAt.2 fun y => tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h1 : Continuous fun x => ‖t x - t y‖ := by
    simp only [@norm_eq_sqrt_re_inner ℂ, inner_sub_sub_self, h]
    fun_prop
  simpa using h1.tendsto y

theorem dense_span_tens {κ H : Type} [Fintype κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (hd : Dense (Submodule.span ℂ (Set.range t) : Set H))
    {ι : Type} (s : ι → ∀ v, E v) (hs : DenseRange s) :
    Dense (Submodule.span ℂ (Set.range fun i => t (s i)) : Set H) := by
  have h1 : Submodule.span ℂ (Set.range t) ≤ (Submodule.span ℂ (Set.range fun i => t (s i))).topologicalClosure := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    refine map_mem_closure (continuous_tens t h) (hs x) ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact dense_closure.1 (hd.mono h1)

theorem eq_of_inner_eq {X H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : X → H)
    (hd : Dense (Submodule.span ℂ (Set.range t) : Set H)) {p q : H} (h : ∀ z, ⟪t z, p⟫_ℂ = ⟪t z, q⟫_ℂ) : p = q := by
  have h0 : innerSL ℂ (p - q) = 0 := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨z, rfl⟩
    rw [innerSL_apply_apply, ContinuousLinearMap.zero_apply, ← inner_conj_symm, inner_sub_right, h z, sub_self,
      map_zero]
  have := congrArg (fun L : H →L[ℂ] ℂ => L (p - q)) h0
  simp only [innerSL_apply_apply, ContinuousLinearMap.zero_apply, inner_self_eq_zero] at this
  exact sub_eq_zero.1 this

theorem inner_update {κ H : Type} [Fintype κ] [DecidableEq κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (z x : ∀ v, E v) (i : κ) (a : E i) :
    ⟪t z, t (Function.update x i a)⟫_ℂ = ⟪z i, a⟫_ℂ * ∏ v ∈ Finset.univ.erase i, ⟪z v, x v⟫_ℂ := by
  rw [h, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

def tensML {κ H : Type} [Fintype κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (hd : Dense (Submodule.span ℂ (Set.range t) : Set H)) :
    ContinuousMultilinearMap ℂ E H where
  toFun := t
  map_update_add' x i a b := by
    refine (eq_of_inner_eq t hd fun z => ?_)
    rw [inner_add_right, inner_update t h, inner_update t h, inner_update t h, inner_add_right, add_mul]
  map_update_smul' x i c a := by
    refine (eq_of_inner_eq t hd fun z => ?_)
    rw [inner_smul_right, inner_update t h, inner_update t h, inner_smul_right, mul_assoc,
      RingHom.id_apply]
  cont := continuous_tens t h

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem denseRange_vec (M : DSModel V S) : DenseRange fun (u : M.Vec) (τ : D.what₂.Tau) => (u τ : M.H τ) := by
  refine (dense_pi Set.univ fun τ _ => Formalism.IndefR.SchurOrthogonalityAlt.sm_dense M τ).mono fun x hx => ?_
  exact ⟨fun τ => ⟨x τ, hx τ trivial⟩, rfl⟩

theorem coe_update [DecidableEq D.what₂.Tau] (u : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    (fun τ' => ((Function.update u τ w τ' : M.sm τ') : M.H τ')) =
      Function.update (fun τ' => (u τ' : M.H τ')) τ (w : M.H τ) := by
  funext τ'
  by_cases h : τ' = τ
  · subst h; simp
  · simp [Function.update_of_ne h]


set_option maxHeartbeats 1000000 in
theorem exists_of_isMultMap (hP : GlobalTheory.Published.CuspRapidDecay) {θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)}
    (hθ : IsInfFam θ) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {T : MMap M}
    (hT : IsMultMap θ M ∅ (fun _ => 1) T) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧
      ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  classical
  have h𝓕 := isFundamentalDomain_stdDom (GQ V) μ
  obtain ⟨c, hc⟩ := GlobalTheory.MultFinite.schurMult (θ := θ) (M := M) (J := ∅) (χ := fun _ => 1) hP μ (stdDom (GQ V))
    hθ inferInstance h𝓕 T (Submodule.subset_span hT) T (Submodule.subset_span hT)
  have hm : ∀ u, MemL2Quotient (GQ V) μ (T u) := by
    intro u
    refine (memL2_iff_fundamental_domain h𝓕).2 ⟨(hT.aut u).left, ?_⟩
    refine (memLp_two_iff_integrable_sq_norm (hT.aut u).cont.measurable.aestronglyMeasurable).2
      ((hc u u).1.norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨F, hFl, hF⟩ : ∃ F : M.Vec → DividedPowerChartLift V μ, (∀ u, lift (GQ V) (F u) =ᵐ[μ] T u) ∧
      ∀ u u', ⟪F u, F u'⟫_ℂ = c * ∏ τ, ⟪(u τ : M.H τ), (u' τ : M.H τ)⟫_ℂ := by
    refine ⟨fun u => (hm u).toL2, fun u => (hm u).lift_toL2_ae_eq, fun u u' => ?_⟩
    rw [← (hc u u').2, MemL2Quotient.inner_toL2_eq_theta_pairing (hm u') (hm u), pet_eq h𝓕 (hT.aut u').left (hT.aut u).left]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [RCLike.star_def]
    ring
  obtain ⟨K, _, _, t0, ht0⟩ := GlobalTheory.HilbTensorExists.exists_pre M.H
  obtain ⟨L, _, _, _, s, hs, hd⟩ := GlobalTheory.HilbTensorExists.exists_complete_dense t0
  have hs' : ∀ x y, ⟪s x, s y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ := fun x y => (hs x y).trans (ht0 x y)
  have hvec := denseRange_vec M
  have hdense := dense_span_tens s hs' hd _ hvec
  have hG : ∀ u u' : M.Vec, ⟪F u, F u'⟫_ℂ = c * ⟪s (fun τ => (u τ : M.H τ)), s (fun τ => (u' τ : M.H τ))⟫_ℂ := fun u u' => by
    rw [hF, hs']
  obtain ⟨A, hA⟩ := exists_extend (ι := M.Vec) (fun u => s fun τ => (u τ : M.H τ)) F hdense c hG
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), ∀ u : M.Vec, Φ (fun τ => (u τ : M.H τ)) = F u :=
    ⟨A.compContinuousMultilinearMap (tensML s hs' hd), hA⟩
  refine ⟨Φ, (mem_homDS hθ).2 ⟨fun y => ?_, fun τ g hg y => ?_⟩, fun u => ?_⟩
  · refine hvec.induction_on y ((Submodule.isClosed_topologicalClosure _).preimage Φ.cont) fun u => ?_
    show Φ _ ∈ GlobalTheory.Cusp.L2cusp V μ
    rw [hΦ u]
    exact GlobalTheory.Cusp.mem_L2cusp_of_ae_eq ⟨(hT.aut u).cont, (hT.aut u).left, hT.cusp u⟩ (hFl u)
  · have h1 : Continuous fun y : (∀ τ, M.H τ) => Φ (Function.update y τ (M.rep τ g (y τ))) :=
      Φ.cont.comp (continuous_id.update τ ((M.rep τ g).continuous.comp (continuous_apply τ)))
    have h2 : Continuous fun y : (∀ τ, M.H τ) => RG V μ (atTau θ V τ g) (Φ y) :=
      (RG V μ (atTau θ V τ g)).continuous.comp Φ.cont
    refine congrFun (hvec.equalizer h1 h2 (funext fun u => ?_)) y
    let w : M.sm τ := ⟨M.rep τ g (u τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ g hg _ (u τ).2⟩
    have e1 := hT.equiv τ g hg u w rfl
    have e2 : Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ g (u τ)) =
        fun τ' => ((Function.update u τ w τ' : M.sm τ') : M.H τ') := (coe_update u τ w).symm
    show Φ (Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ g (u τ))) =
      RG V μ (atTau θ V τ g) (Φ fun τ' => (u τ' : M.H τ'))
    rw [e2, hΦ (Function.update u τ w), hΦ u]
    refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
    refine (hFl _).trans ?_
    rw [e1]
    refine (EventuallyEq.trans ?_ (lift_R _ _).symm)
    exact ((measurePreserving_mul_right μ (atTau θ V τ g)).quasiMeasurePreserving.ae (hFl u)).mono
      fun x hx => hx.symm
  · rw [hΦ u]
    exact hFl u

theorem eq_of_represents {μ : Measure (GA D V)} [μ.IsHaarMeasure] {T : MMap M}
    {Φ Φ' : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)}
    (h : ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v)
    (h' : ∀ v : M.Vec, lift (GQ V) (Φ' fun τ => (v τ : M.H τ)) =ᵐ[μ] T v) : Φ = Φ' := by
  refine ContinuousMultilinearMap.ext fun y => congrFun ((denseRange_vec M).equalizer Φ.cont Φ'.cont
    (funext fun v => ?_)) y
  exact l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((h v).trans (h' v).symm)

theorem exists_of_mem (hP : GlobalTheory.Published.CuspRapidDecay) {θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)}
    (hθ : IsInfFam θ) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {T : MMap M}
    (hT : T ∈ GlobalTheory.CuspMult.allMaps θ M) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧
      ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact exists_of_isMultMap hP hθ μ hT
  | zero =>
    refine ⟨0, zero_mem _, fun v => ?_⟩
    simp only [ContinuousMultilinearMap.zero_apply, MultilinearMap.zero_apply]
    exact ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)
  | add T T' _ _ ih ih' =>
    obtain ⟨Φ, h1, h2⟩ := ih
    obtain ⟨Φ', h1', h2'⟩ := ih'
    refine ⟨Φ + Φ', add_mem h1 h1', fun v => ?_⟩
    simp only [ContinuousMultilinearMap.add_apply, MultilinearMap.add_apply]
    exact Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add _ _)) ((h2 v).add (h2' v))
  | smul a T _ ih =>
    obtain ⟨Φ, h1, h2⟩ := ih
    refine ⟨a • Φ, Submodule.smul_mem _ a h1, fun v => ?_⟩
    simp only [ContinuousMultilinearMap.smul_apply, MultilinearMap.smul_apply]
    exact Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul a _)) ((h2 v).const_smul a)

theorem existsUnique_intertwiner : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ T ∈ GlobalTheory.CuspMult.allMaps θ M, ∃! Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  intro hP D θ hθ V S M μ _ _ T hT
  obtain ⟨Φ, h1, h2⟩ := exists_of_mem hP hθ μ hT
  exact ⟨Φ, ⟨h1, h2⟩, fun Φ' h' => eq_of_represents h'.2 h2⟩

end GlobalTheory.CuspIntertwiner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicUnitaryPointExtLocalComponents
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.TrFinExt

private theorem eq_of_finE_map_prV_eq_forall_place {D : D7} (V : HSp D) (a b : GA D V)
    (h : ∀ u : HeightOneSpectrum (𝓞 D.host.F), (Formalism.IndefR.Lev.finE V a).val.map (Formalism.UG.prV (E := D.host.E) u) = (Formalism.IndefR.Lev.finE V b).val.map (Formalism.UG.prV (E := D.host.E) u))
    (i j : Fin V.rank) :
    (Formalism.IndefR.Lev.finE V a).val i j = (Formalism.IndefR.Lev.finE V b).val i j := by

  rw [← sub_eq_zero]
  refine Formalism.UG.P.afsplit_inj _ fun w => ?_
  have hw := congrFun (congrFun (h w) i) j
  rw [Matrix.map_apply, Matrix.map_apply] at hw
  rw [map_sub, hw, sub_self]

theorem gfc_ext : ∀ {D : D7} (V : HSp D) (x y : GfC V), (∀ u : HeightOneSpectrum (𝓞 D.host.F), (Formalism.IndefR.Lev.finE V (x : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = (Formalism.IndefR.Lev.finE V (y : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u)) → x = y := by
  intro D V x y h

  have hx : infHom V (x : GA D V) = 1 := x.2
  have hy : infHom V (y : GA D V) = 1 := y.2
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply GlobalTheory.FinIsoGrp.proj_inj D
  · have ex := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => g.val i j) hx
    have ey := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => g.val i j) hy
    exact ex.trans ey.symm
  · have e := eq_of_finE_map_prV_eq_forall_place V (x : GA D V) (y : GA D V) h i j
    rw [GlobalTheory.FinIsoGrp.finE_val, GlobalTheory.FinIsoGrp.finE_val] at e
    exact e

end GlobalTheory.TrFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentNe
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.LocFinComp

theorem prV_swap_snd {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (u : HeightOneSpectrum (𝓞 F)) (x : AF F ⊗[F] E) :
    Formalism.UG.prV (E := E) u (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x)) =
    Algebra.TensorProduct.comm F (Fv F u) E (Algebra.TensorProduct.map (evFin F u) (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => exact Eq.refl _
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem finE_locFin_map_prV_ne : ∀ {D : D7} (V : HSp D) {v u : HeightOneSpectrum (𝓞 D.host.F)}, u ≠ v → ∀ (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = 1 := by
  intro D V v u huv g
  have hp : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u (locFin V v g : GA D V) = 1 :=
    GlobalTheory.AdelicU.proj_emb_ne D.sp.cm.sig V.gram huv g
  have hm := congrArg (fun y => (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram y).val) hp
  simp only [GlobalTheory.AdelicU.matHom_proj, map_one, Units.val_one] at hm
  ext i j
  have hij := congrFun (congrFun hm i) j
  have key := prV_swap_snd (F := D.host.F) (E := D.host.E) u
    ((Formalism.L2.Theta.matHom V (locFin V v g : GA D V)).val i j)
  refine key.trans ((congrArg (Algebra.TensorProduct.comm _ _ _) hij).trans ?_)
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

end GlobalTheory.LocFinComp
end

