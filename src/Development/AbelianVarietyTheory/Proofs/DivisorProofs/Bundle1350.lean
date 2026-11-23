module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInfiniteDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstants
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.LinFormBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem nnnorm_sum_le (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι) (x : ι → Fv F v) {c : ℝ≥0}
    (h : ∀ i ∈ s, ‖x i‖₊ ≤ c) : ‖∑ i ∈ s, x i‖₊ ≤ c := by
  rw [← absFin_tmul_one (E := F) F v, TensorProduct.sum_tmul]
  exact absFin_sum_le F v _ _ fun i hi => (absFin_tmul_one (E := F) F v (x i)).trans_le (h i hi)

theorem eventually_nnnorm_evFin_le_one (a : AF F) : ∀ᶠ v in Filter.cofinite, ‖evFin F v a‖₊ ≤ 1 := by
  refine (eventually_absFin_le_one (E := F) F (a ⊗ₜ[F] (1 : F))).mono fun v hv => ?_
  rwa [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    absFin_tmul_one] at hv

theorem exists_bound {n m : ℕ} (f : Matrix (Fin n) (Fin m) (AF F ⊗[F] E) →ₗ[AF F] AF F) :
    ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧
      ∀ X v, ‖evFin F v (f X)‖₊ ≤
        K v * Finset.univ.sup fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2)) := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  let B := Algebra.TensorProduct.basis (AF F) b.traceDual

  let y : Fin n × Fin m × s → AF F := fun q => f (Matrix.single q.1 q.2.1 (B q.2.2))
  let K : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (Finset.univ.sup fun q => ‖evFin F v (y q)‖₊)
  have hdec : ∀ X : Matrix (Fin n) (Fin m) (AF F ⊗[F] E),
      f X = ∑ q : Fin n × Fin m × s, B.repr (X q.1 q.2.1) q.2.2 * y q := by
    intro X
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← B.sum_repr (X i j)]
    have : Matrix.single i j (∑ k, B.repr (X i j) k • B k) = ∑ k, B.repr (X i j) k • Matrix.single i j (B k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← Matrix.singleLinearMap_apply (R := AF F), map_sum, map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp only [map_smul, smul_eq_mul, y]
  refine ⟨K, ?_, fun v => le_max_left _ _, fun X v => ?_⟩
  · have h := eventually_all.2 fun q => eventually_nnnorm_evFin_le_one (y q)
    refine (eventually_cofinite.1 h).subset fun v hv hv' => hv (max_eq_left (Finset.sup_le fun q _ => ?_))
    exact hv' q
  · have hsup : ∀ p : Fin n × Fin m, absFin F v (compFin F E v (X p.1 p.2)) ≤
        Finset.univ.sup fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2)) :=
      fun p => Finset.le_sup (f := fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2)))
        (Finset.mem_univ p)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdec X, map_sum]
    refine nnnorm_sum_le v _ _ fun q _ => ?_
    rw [map_mul, nnnorm_mul, mul_comm]
    refine mul_le_mul' ?_ ?_
    · exact (Finset.le_sup (f := fun q => ‖evFin F v (y q)‖₊) (Finset.mem_univ q)).trans (le_max_right _ _)
    · rw [← HeightProper.repr_map b.traceDual (evFin F v) (X q.1 q.2.1) q.2.2]
      refine (HeightProper.nnnorm_repr_le_absFin b hb' v _ q.2.2).trans ?_
      have hc : Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (X q.1 q.2.1) = compFin F E v (X q.1 q.2.1) :=
        rfl
      rw [hc]
      exact hsup (q.1, q.2.1)

end GlobalTheory.LinFormBound

theorem GlobalTheory.LinFormBound.main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) :=
  fun f => GlobalTheory.LinFormBound.exists_bound f
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocGLMemKglob
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerTwSplit
open GlobalTheory.EulerTw GlobalTheory.EulerTwU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem theta_mem {v w : Pl E} (f : v.adicCompletion E →+* w.adicCompletion E) (hf : ∀ x, Valued.v (f x) = Valued.v x)
    {g : GLw n v} (hg : g ∈ GlobalTheory.LFun.KGL v (n := n)) :
    thetaGL n (RingHom.id _) (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) (GeneralLinearGroup.map f g) =
      GeneralLinearGroup.map f g := Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) (GeneralLinearGroup.map f g)) * (PhiU n _)⁻¹ ∈ _
  rw [hid]
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n) (GlobalTheory.BCT.LocGlue.intst E n v w f hf g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))


end GlobalTheory.EulerTwSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormAtSplitPlace
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocalNormSplit

theorem exists_sq_of_split (E : Type) [Field E] [NumberField E] [IsCMField E]
    (θ : E) (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧
      w'.under (𝓞 (maximalRealSubfield E)) = v)
    (d : maximalRealSubfield E) (hd : (d : E) = θ * θ) :
    ∃ s : v.adicCompletion (maximalRealSubfield E),
      s * s = algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) d := by
  classical
  by_contra hns
  push_neg at hns
  obtain ⟨w, w', hne, hw, hw'⟩ := hv
  obtain ⟨ψ, -, hb, -⟩ := GlobalTheory.TraceClasses.exists_finite_decomp (maximalRealSubfield E) E
  have hθF : ∀ a : maximalRealSubfield E, (a : E) ≠ θ := by
    intro a ha
    have h1 : IsCMField.complexConj E (a : E) = a := (IsCMField.complexConj_eq_self_iff E _).2 a.2
    rw [ha, hθ] at h1
    exact hθ0 (by linear_combination -h1 / 2)
  have hli : LinearIndependent (maximalRealSubfield E) ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro p q hpq
    by_cases hq : q = 0
    · subst hq
      simpa using hpq
    · exfalso
      refine hθF (-p / q) ?_
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hpq
      have hq' : (q : E) ≠ 0 := by simpa using hq
      change ((-p / q : maximalRealSubfield E) : E) = θ
      push_cast
      field_simp
      rw [show algebraMap _ E p = p from rfl, show algebraMap _ E q = q from rfl] at hpq
      linear_combination -hpq
  let b := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two])
  set K := v.adicCompletion (maximalRealSubfield E)
  let bA := Algebra.TensorProduct.basis K b
  let t : K ⊗[maximalRealSubfield E] E := 1 ⊗ₜ θ
  have hb0 : bA 0 = 1 := by
    simp [bA, b, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.one_def]
  have hb1 : bA 1 = t := by
    simp [bA, b, Algebra.TensorProduct.basis_apply, t]
  have li : ∀ p q : K, algebraMap K _ p + algebraMap K _ q * t = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have := Fintype.linearIndependent_iff.1 bA.linearIndependent ![p, q] (by
      rw [Fin.sum_univ_two, hb0, hb1]
      simpa [Algebra.smul_def] using h)
    exact ⟨by simpa using this 0, by simpa using this 1⟩
  have sp : ∀ y, y = algebraMap K _ (bA.repr y 0) + algebraMap K _ (bA.repr y 1) * t := by
    intro y
    conv_lhs => rw [← bA.sum_repr y]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
  have htt : t * t = algebraMap K _ (algebraMap (maximalRealSubfield E) K d) := by
    rw [← IsScalarTower.algebraMap_apply]
    change (1 : K) ⊗ₜ θ * (1 : K) ⊗ₜ θ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd]
    exact (Algebra.TensorProduct.includeRight.commutes d)
  let W := {u : HeightOneSpectrum (𝓞 E) // u.under (𝓞 (maximalRealSubfield E)) = v}
  let w₀ : W := ⟨w, hw⟩
  let w₁ : W := ⟨w', hw'⟩
  have h01 : w₀ ≠ w₁ := fun h => hne (congrArg Subtype.val h)
  let e₀ : ∀ u : W, u.1.adicCompletion E := Pi.single (M := fun u : W => u.1.adicCompletion E) w₀ 1
  let e₁ : ∀ u : W, u.1.adicCompletion E := Pi.single (M := fun u : W => u.1.adicCompletion E) w₁ 1
  obtain ⟨u₀, hu₀⟩ := (hb v).2 e₀
  obtain ⟨u₁, hu₁⟩ := (hb v).2 e₁
  have hprod : u₀ * u₁ = 0 := by
    apply (hb v).1
    funext u
    simp only [map_mul, map_zero]
    rw [show ψ v u u₀ = e₀ u from congrFun hu₀ u, show ψ v u u₁ = e₁ u from congrFun hu₁ u]
    by_cases h : u = w₀
    · subst h
      simp [e₁, Pi.single_apply, h01]
    · simp [e₀, Pi.single_apply, h]
  have hn₀ : u₀ ≠ 0 := by
    rintro rfl
    have := congrFun hu₀ w₀
    simp [e₀] at this
  have hn₁ : u₁ ≠ 0 := by
    rintro rfl
    have := congrFun hu₁ w₁
    simp [e₁] at this
  obtain ⟨a, b', hu0⟩ : ∃ a b' : K, u₀ = algebraMap K _ a + algebraMap K _ b' * t := ⟨_, _, sp u₀⟩
  obtain ⟨c, e, hu1⟩ : ∃ c e : K, u₁ = algebraMap K _ c + algebraMap K _ e * t := ⟨_, _, sp u₁⟩
  set d' := algebraMap (maximalRealSubfield E) K d
  have ha : ¬ (a = 0 ∧ b' = 0) := by
    rintro ⟨h1, h2⟩
    apply hn₀
    rw [hu0, h1, h2]
    simp
  have hc : ¬ (c = 0 ∧ e = 0) := by
    rintro ⟨h1, h2⟩
    apply hn₁
    rw [hu1, h1, h2]
    simp
  have heq := li (a * c + d' * b' * e) (a * e + b' * c) (by
    rw [← hprod, hu0, hu1]
    simp only [map_add (f := _), map_mul]
    linear_combination (-(algebraMap K _ b' * algebraMap K _ e)) * htt)
  have hz : c * c - d' * e * e = 0 := by
    by_contra hz
    apply ha
    constructor
    · refine (mul_eq_zero.1 (?_ : a * (c * c - d' * e * e) = 0)).resolve_right hz
      linear_combination c * heq.1 - d' * e * heq.2
    · refine (mul_eq_zero.1 (?_ : b' * (c * c - d' * e * e) = 0)).resolve_right hz
      linear_combination -(e * heq.1) + c * heq.2
  by_cases he : e = 0
  · apply hc
    refine ⟨?_, he⟩
    rw [he] at hz
    simpa using hz
  · apply hns (c / e)
    field_simp
    linear_combination hz

theorem exists_norm_of_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r) (x : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q), GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q x = x → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v) → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ x := by
  intro E _ _ _ r Q x hx v hv
  obtain ⟨θ, hθ0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  have hθ' : IsCMField.complexConj E θ = -θ := hθ
  have hdmem : θ * θ ∈ maximalRealSubfield E :=
    (IsCMField.complexConj_eq_self_iff E _).1 (by rw [map_mul, hθ']; ring)
  let K := v.adicCompletion (maximalRealSubfield E)
  obtain ⟨d, hd⟩ : ∃ d : maximalRealSubfield E, (d : E) = θ * θ := ⟨⟨_, hdmem⟩, rfl⟩
  obtain ⟨s, hs⟩ := exists_sq_of_split E θ hθ0 hθ' v hv d hd
  let B := K ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero, eq_comm] at hs
    have h1 := (_root_.map_eq_zero (algebraMap (maximalRealSubfield E) K)).1 hs
    rw [h1] at hd
    exact hθ0 (mul_self_eq_zero.1 (by simpa using hd.symm))
  let uT : B := 1 ⊗ₜ algebraMap E _ θ
  have hTT : uT * uT = algebraMap K B (s * s) := by
    rw [hs, ← IsScalarTower.algebraMap_apply]
    change (1 : K) ⊗ₜ algebraMap E _ θ * (1 : K) ⊗ₜ algebraMap E _ θ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul, ← hd,
      show (d : E) = algebraMap (maximalRealSubfield E) E d from rfl,
      ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes _)
  let uc : B := algebraMap K B s⁻¹ * uT
  have hc : uc * uc = 1 := by
    have : uc * uc = algebraMap K B (s⁻¹ * s⁻¹ * (s * s)) := by
      rw [map_mul, map_mul, ← hTT]; ring
    rw [this, show s⁻¹ * s⁻¹ * (s * s) = 1 by rw [← mul_inv, inv_mul_cancel₀ (mul_ne_zero hs0 hs0)], map_one]
  have hiT : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K uT = -uT := by
    change Algebra.TensorProduct.map _ _ ((1 : K) ⊗ₜ algebraMap E _ θ) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_algebraMap, hθ',
      map_neg, TensorProduct.tmul_neg]
  have hic : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K uc = -uc := by
    change GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K (algebraMap K B s⁻¹ * uT) = -(algebraMap K B s⁻¹ * uT)
    rw [map_mul, AlgHom.commutes, hiT, mul_neg]
  have hiX : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K (1 ⊗ₜ x) = 1 ⊗ₜ x := by
    change Algebra.TensorProduct.map _ _ ((1 : K) ⊗ₜ x) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hx]
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap (maximalRealSubfield E) K) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  let hf : B := algebraMap K B 2⁻¹
  have hh : hf * 2 = 1 := by
    rw [← map_ofNat (algebraMap K B) 2, ← map_mul, inv_mul_cancel₀ h2K, map_one]
  have hih : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K hf = hf := AlgHom.commutes _ _
  refine ⟨hf * (1 + uc) * (1 ⊗ₜ x) + hf * (1 - uc), ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_mul, map_add (f := _), map_sub, map_one, hic, hiX, hih]
  linear_combination (hf ^ 2 * (2 * (1 ⊗ₜ x : B) - (1 ⊗ₜ x : B) ^ 2 - 1)) * hc + ((2 * hf + 1) * (1 ⊗ₜ x : B)) * hh

end GlobalTheory.LocalNormSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTwist_continuous_involution_integral_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ (∀ g, thL n w (thL n w g) = g) ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), thL n w k ∈ GlobalTheory.LFun.KGL w (n := n)) ∧ (∀ g y, nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g) ∧ IsOpen (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ (∀ δ : GL (Fin n) E, (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly) ∧ ∀ x ∈ locU n w, cLoc w x ∈ UL n w := by
  first | exact @GlobalTheory.BCT.ThBasic.twist_basic | exact GlobalTheory.BCT.ThBasic.twist_basic | (intros; apply GlobalTheory.BCT.ThBasic.twist_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantEqOfFirstColumnsChange
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph
open scoped ComplexConjugate
open scoped Matrix

namespace GlobalTheory.MajCols

theorem hermC_comb_right {E : Type} [Field E] {r p : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (v : Fin r → ℂ) (k : Fin p → ℂ) (u : Fin p → Fin r → ℂ) :
    hermC τ G v (∑ c, k c • u c) = ∑ c, conj (k c) * hermC τ G v (u c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

theorem hermC_comb_left {E : Type} [Field E] {r p : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (v : Fin r → ℂ) (k : Fin p → ℂ) (u : Fin p → Fin r → ℂ) :
    hermC τ G (∑ c, k c • u c) v = ∑ c, k c * hermC τ G (u c) v := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

theorem quad_change {p : ℕ} (A B D : Matrix (Fin p) (Fin p) ℂ) (hB : B.det ≠ 0) (hD : D.det ≠ 0)
    (w w' : Fin p → ℂ) :
    (w ᵥ* D) ⬝ᵥ ((B * A * D)⁻¹ *ᵥ (B *ᵥ w')) = w ⬝ᵥ (A⁻¹ *ᵥ w') := by
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hD' : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  congr 2
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hD', Matrix.nonsing_inv_mul_cancel_right _ _ hB']

theorem sum_eq_dot {p : ℕ} (M : Matrix (Fin p) (Fin p) ℂ) (w w' : Fin p → ℂ) :
    ∑ a, ∑ b, w a * M a b * w' b = w ⬝ᵥ (M *ᵥ w') := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem maj_eq_of_cols :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x' y : Frame X.Ψ r)
    (τ : X.Ψ) (C : Matrix (Fin X.p0) (Fin X.p0) ℂ), C.det ≠ 0 → (X.gramPos y τ).det ≠ 0 →
    (∀ a : Fin X.p0, col (mat x' τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, C c a • col (mat y τ) (Fin.castLE X.p0_le c)) →
    ∀ v : Fin r → ℂ, X.maj x' τ v = X.maj y τ v := by
  intro E _ _ _ r X x' y τ C hC _ hcol v
  set w : Fin X.p0 → ℂ := fun a => hermC τ.1 X.Gm v (col (mat y τ) (Fin.castLE X.p0_le a)) with hw
  have hD : (C.map (starRingEnd ℂ)).det ≠ 0 := by
    have := (starRingEnd ℂ).map_det C
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero _).mpr hC
  have hB : (Cᵀ).det ≠ 0 := by rwa [Matrix.det_transpose]
  have h1 : (fun a => hermC τ.1 X.Gm v (col (mat x' τ) (Fin.castLE X.p0_le a))) =
      w ᵥ* C.map (starRingEnd ℂ) := by
    funext a
    rw [hcol, hermC_comb_right]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, hw]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have h2 : (fun a => conj (hermC τ.1 X.Gm v (col (mat x' τ) (Fin.castLE X.p0_le a)))) =
      Cᵀ *ᵥ fun a => conj (w a) := by
    funext a
    rw [hcol, hermC_comb_right]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hw, map_sum, map_mul,
      Complex.conj_conj]
  have h3 : X.gramPos x' τ = Cᵀ * X.gramPos y τ * C.map (starRingEnd ℂ) := by
    ext a b
    simp only [Data.gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.map_apply]
    rw [hcol a, hcol b, hermC_comb_right]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hermC_comb_left, mul_comm]
  have key : X.posPart x' τ v = X.posPart y τ v := by
    unfold Data.posPart
    congr 1
    rw [sum_eq_dot (X.gramPos x' τ)⁻¹
        (fun a => hermC τ.1 X.Gm v (col (mat x' τ) (Fin.castLE X.p0_le a)))
        (fun a => conj (hermC τ.1 X.Gm v (col (mat x' τ) (Fin.castLE X.p0_le a)))),
      sum_eq_dot (X.gramPos y τ)⁻¹ w (fun a => conj (w a)), h1, h2, h3,
      quad_change _ _ _ hB hD]
  unfold Data.maj
  rw [key]

end GlobalTheory.MajCols
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
section
noncomputable section

namespace GlobalTheory.IwLine

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem UG_eq_HR (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.WeilM.UG (cA σ) (incM F J) = HR (AF F) σ Jᵀ := by
  have hc : ∀ M : Matrix (Fin n) (Fin n) (AE F E), M.map (cA σ) = M.map (sigR (AF F) σ) := fun M => by
    ext i j; exact cA_eq_sigR σ _
  have hJ : JR (AF F) Jᵀ = (incM F J)ᵀ := rfl
  ext g
  change (g.1)ᵀ * incM F J * (g.1).map (cA σ) = incM F J ↔ cT (sigR (AF F) σ) g.1 * JR (AF F) Jᵀ * g.1 = JR (AF F) Jᵀ
  rw [hc, hJ, cT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def ofGAd : GAd σ Jᵀ ≃* UA σ J := MulEquiv.subgroupCongr (UG_eq_HR σ J).symm

theorem mat_ofGAd (g : GAd σ Jᵀ) : mat (ofGAd σ J g) = (matHom (AF F) σ Jᵀ g).1 := rfl

def lineStab (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {g | ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x}
  one_mem' := ⟨1, by simp [mat, Matrix.one_mulVec]⟩
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨b * a, ?_⟩
    show (mat g * mat h) *ᵥ incV F x = _
    rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul, ha, smul_smul, Units.val_mul]
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    have e : mat g⁻¹ *ᵥ (mat g *ᵥ incV F x) = incV F x := by
      rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_smul] at e
    calc mat g⁻¹ *ᵥ incV F x = ((a⁻¹ : (AE F E)ˣ) : AE F E) • ((a : AE F E) • mat g⁻¹ *ᵥ incV F x) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e]

theorem mem_lineStab {x : Fin n → E} {g : UA σ J} :
    g ∈ lineStab σ J x ↔ ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x := Iff.rfl

end GlobalTheory.IwLine
end
end

