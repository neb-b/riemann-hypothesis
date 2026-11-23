module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralArchimedeanMatricesLeftMulJacobian
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem integral_eq_integral_mulLeft_matrixInf (E : Type) [Field E] [NumberField E] (n : ℕ)
    (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ) :
    ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
      F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  set W := InfinitePlace E
  set M : Matrix (Fin n) (Fin n) (Cinf E) := (A : Matrix (Fin n) (Fin n) (Cinf E)) with hM
  set L : (Fin n → Fin n → Cinf E) →ₗ[ℝ] (Fin n → Fin n → Cinf E) :=
    { toFun := fun x i j => (M * Matrix.of x) i j
      map_add' := fun x y => by
        funext i j
        change (M * (Matrix.of x + Matrix.of y)) i j = (M * Matrix.of x) i j + (M * Matrix.of y) i j
        rw [mul_add, Matrix.add_apply]
      map_smul' := fun c x => by
        funext i j
        change (M * (c • Matrix.of x)) i j = c • (M * Matrix.of x) i j
        rw [Matrix.mul_smul, Matrix.smul_apply] } with hLdef
  have hL : ∀ h, L h = fun i j => (M * Matrix.of h) i j := fun h => rfl

  let e : (Fin n → Fin n → Cinf E) ≃ₗ[ℝ] (W → Fin n → Fin n → ℂ) :=
    { toFun := fun h w i j => h i j w
      invFun := fun g i j w => g w i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Lw : W → (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) := fun w =>
    (LinearMap.mulLeft ℂ (M.map (fun z => z w))).restrictScalars ℝ
  have hconj : (e : _ →ₗ[ℝ] _) ∘ₗ L ∘ₗ (e.symm : _ →ₗ[ℝ] _) =
      LinearMap.pi (fun w => Lw w ∘ₗ LinearMap.proj w) := by
    apply LinearMap.ext; intro g; funext w i j
    change (M * Matrix.of (fun i j w => g w i j)) i j w = (M.map (fun z => z w) * Matrix.of (g w)) i j
    simp [Matrix.mul_apply, Finset.sum_apply, Matrix.map_apply]
  have hdetw : ∀ w, LinearMap.det (Lw w) = Complex.normSq (M.det w) ^ n := by
    intro w
    have := GroundTheory.Automorphic.det_restrictScalars_mulLeft (M.map (fun z => z w))
    rw [Fintype.card_fin, ← Complex.normSq_eq_norm_sq] at this
    show LinearMap.det ((LinearMap.mulLeft ℂ (M.map fun z => z w)).restrictScalars ℝ) = _
    rw [this]
    congr 2
    exact (RingHom.map_det (Pi.evalRingHom (fun _ : W => ℂ) w) M).symm
  have hdet : LinearMap.det L = jacInf M := by
    rw [← LinearMap.det_conj L e, hconj, LinearMap.det_pi]
    simp only [hdetw]
    rfl
  have hpos : 0 < jacInf M := by
    have hdA : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
    refine Finset.prod_pos fun w _ => pow_pos (Complex.normSq_pos.2 ?_) n
    intro h0
    have hu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    have : IsUnit (M.det w) := hu.map (Pi.evalRingHom (fun _ : W => ℂ) w)
    exact this.ne_zero h0
  have hd0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap : Measure.map L (volume : Measure (Fin n → Fin n → Cinf E)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd0
  set Le : (Fin n → Fin n → Cinf E) ≃L[ℝ] (Fin n → Fin n → Cinf E) :=
    (LinearMap.equivOfDetNeZero L hd0).toContinuousLinearEquiv
  have hLe : (Le : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) = L := rfl
  have hemb : MeasurableEmbedding (L : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) := by
    rw [← hLe]; exact Le.toHomeomorph.measurableEmbedding
  simp_rw [← hL]
  rw [integral_const_mul, ← hemb.integral_map, hmap, integral_smul_measure, hdet,
    abs_of_pos (inv_pos.2 hpos), ENNReal.toReal_ofReal (inv_pos.2 hpos).le, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hpos.ne'), one_mul]

end GlobalTheory.JSW.MirCinf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqZero
section
namespace GlobalTheory.RowPartsOrth

section Generic
open MeasureTheory Formalism.IndefR.Bridge GlobalTheory.DoubleCosetAdjoint

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)

variable {μ Γ 𝓕}



theorem isDC_of_local {H : Type} [Group H] (J L : Subgroup H) (x : H) (A : Finset H) (hx : x ∈ L)
    (hs : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hL : ∀ a ∈ A, a ∈ L) (hA : IsDC (J ⊓ L) x A) : IsDC J x A := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, k₂, e⟩ := hA.1 a ha
    exact ⟨⟨k₁, k₁.2.1⟩, ⟨k₂, k₂.2.1⟩, e⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ha, b, hb, haL, e, hc⟩ := hs k₁ k₁.2
    have e2 : (k₁ : H) * x * k₂ = a * x * (b * k₂) := by
      rw [e, mul_assoc a b x, (hc x hx).eq]; simp only [mul_assoc]
    obtain ⟨r, ⟨hr, hr2⟩, hu⟩ := hA.2 (a * x) ⟨⟨a, ha, haL⟩, 1, by simp⟩
    rw [e2]
    refine ⟨r, ⟨hr, ?_⟩, fun r' hr' => hu r' ⟨hr'.1, ?_, ?_⟩⟩
    · have := J.mul_mem hr2.1 (J.mul_mem hb k₂.2)
      simpa only [mul_assoc] using this
    · have := J.mul_mem hr'.2 (J.inv_mem (J.mul_mem hb k₂.2))
      simpa [mul_assoc] using this
    · exact L.mul_mem (L.inv_mem (hL r' hr'.1)) (L.mul_mem haL hx)

end Generic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx NumberField IsDedekindDomain Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RowPartsOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProof
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDer

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth
  GlobalTheory.IsoTriv

section Two

variable {K : Type} [Field K] [CharZero K] {d : ℕ}

theorem subst_secondBlockZero_twoPointVariables {ι : Type} (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0)
    (f : PS K 2 d) :
    subst Y (subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (subst (twoVars K d) f : MvPowerSeries (Fin d ⊕ Fin d) K) :
        MvPowerSeries (Fin d) K) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) f := by
  have hYs : HasSubst Y := hasSubst_of_constantCoeff_zero hY
  have hA := GlobalTheory.LogJacobian.hasSubst_substSecondBlockZero (C := K) d
  have hB : HasSubst (fun q : Fin 2 × Fin d => subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (twoVars K d q)) :=
    hasSubst_of_constantCoeff_zero fun q =>
      constantCoeff_subst_eq_zero hA (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d) (cc_twoVars q)
  rw [subst_comp_subst_apply hs_twoVars hA, subst_comp_subst_apply hB hYs]
  congr 1
  funext q
  rw [twoVars, subst_X hA]
  split_ifs with h
  · simp [GlobalTheory.LogJacobian.substSecondBlockZero, subst_X hYs]
  · simp only [GlobalTheory.LogJacobian.substSecondBlockZero, Sum.elim_inr]
    rw [← coe_substAlgHom hYs, map_zero]

theorem pderiv_inr_twoVars (k : Fin d) (f : PS K 2 d) :
    pderiv (Sum.inr k) (subst (twoVars K d) f) = subst (twoVars K d) (pderiv ((1 : Fin 2), k) f) := by
  classical
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst cc_twoVars, Finset.sum_eq_single ((1 : Fin 2), k)]
  · simp [twoVars]
  · intro q _ hq
    obtain ⟨a, i⟩ := q
    fin_cases a
    · simp [twoVars]
    · have : i ≠ k := fun h => hq (by simp [h])
      simp [twoVars, this]
  · simp

end Two

section Main

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℝ)} {d n : ℕ} {ι : Type}

theorem subst_jacEntry (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0) (k j : Fin d) :
    subst Y (GlobalTheory.LogJacobian.jacEntry (logFGLOf v F hF) k j) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) (pderiv ((1 : Fin 2), k) (F.F j)) := by
  rw [← subst_secondBlockZero_twoPointVariables Y hY, ← pderiv_inr_twoVars]
  rfl


omit [CharZero K] in
theorem subst_ev_pt_zero [Finite ι] (T : Fin n × Fin d → MvPowerSeries ι K) (hT : ∀ q, constantCoeff (T q) = 0)
    (b : Fin n) (g : PS K 2 d) :
    subst T (ev (n := n) ![pt K d b, 0] g) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then T (b, q.2) else 0) g := by
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h2 : HasSubst (fun p : Fin 2 × Fin d => (![pt K d b, 0] : Fin 2 → Pt K n d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j <;> simp [pt]
  unfold ev
  rw [subst_comp_subst_apply h2 hTs]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  · simp [pt, subst_X hTs]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply, one_ne_zero, ite_false]
    rw [← coe_substAlgHom hTs, map_zero]


omit [CharZero K] in
theorem constantCoeff_subst_self {σ : Type} [Finite σ] (T : σ → MvPowerSeries ι K)
    (hT : ∀ q, constantCoeff (T q) = 0) (f : MvPowerSeries σ K) :
    constantCoeff (subst T f : MvPowerSeries ι K) = constantCoeff f := by
  have hs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h0 : constantCoeff (subst T (f - (constantCoeff f) • 1) : MvPowerSeries ι K) = 0 :=
    constantCoeff_subst_eq_zero hs hT (by simp)
  rw [← coe_substAlgHom hs, map_sub, map_smul, map_one, coe_substAlgHom hs] at h0
  simpa [sub_eq_zero] using h0

variable [Fintype ι]

def logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) : Fin d → MvPowerSeries ι K :=
  fun e => ∑ l, (if cp l = b then u l e else 0) • (X l : MvPowerSeries ι K)

omit [CharZero K] in
theorem cc_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) :
    constantCoeff (logLin cp u b e) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [logLin, map_sum, constantCoeff_smul, constantCoeff_X, smul_zero, Finset.sum_const_zero]

omit [CharZero K] in
theorem pderiv_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) (l : ι) :
    pderiv l (logLin cp u b e) = if cp l = b then C (u l e) else 0 := by
  classical
  unfold logLin
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single l]
  · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
    split_ifs <;> simp
  · intro l' _ hl
    rw [Derivation.map_smul, pderiv_X_of_ne hl, smul_zero]
  · simp

theorem pderiv_subst_expPt (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (cp : ι → Fin n) (u : ι → Fin d → K) (l : ι) (Φ : PS K n d) :
    subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) (DofN F.F (cp l) (u l) Φ) =
      pderiv l (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ) := by
  classical
  set G := logFGLOf v F hF with hG
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt G (logLin cp u q.1) q.2 with hTdef
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt G (cc_logLin cp u q.1) q.2
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have key : ∀ b j, pderiv l (T (b, j)) = if cp l = b then
      ∑ i : Fin d, C (u l i) * subst T (ev (n := n) ![pt K d b, 0] (pderiv ((1 : Fin 2), i) (F.F j))) else 0 := by
    intro b j
    have h1 : pderiv l (T (b, j)) = ∑ i, subst (logLin cp u b) (pderiv i (expOf G j)) *
        pderiv l (logLin cp u b i) :=
      ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (cc_logLin cp u b) (expOf G j) l
    have h2 : ∀ i, subst (logLin cp u b) (pderiv i (expOf G j)) =
        subst T (ev (n := n) ![pt K d b, 0] (pderiv ((1 : Fin 2), i) (F.F j))) := by
      intro i
      rw [GlobalTheory.LogJacobian.pderiv_expOf, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G).1)
        (hasSubst_of_constantCoeff_zero (cc_logLin cp u b)), subst_ev_pt_zero T hT]
      exact subst_jacEntry F hF (fun e => T (b, e)) (fun e => hT (b, e)) i j
    rw [h1]
    simp only [h2, pderiv_logLin]
    split_ifs
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · simp
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hT, Fintype.sum_prod_type, Finset.sum_eq_single (cp l)]
  · unfold DofN
    simp only [key, ite_true]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coe_substAlgHom hTs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, coe_substAlgHom hTs, subst_C]
  · intro b _ hb
    simp [key, Ne.symm hb]
  · simp

end Main

theorem invDer : InvDerSt := by
  intro K _ _ v d F hF n ι _ cp u P Φ
  classical
  show _ = derivAt0 P (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ)
  have hk := pderiv_subst_expPt F hF cp u
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt _ (cc_logLin cp u q.1) q.2
  have hit : ∀ (l : ι) (c : ℕ) (g : PS K n d),
      subst T ((DofN F.F (cp l) (u l))^[c] g) = (pderiv l)^[c] (subst T g : MvPowerSeries ι K) := by
    intro l c
    induction c with
    | zero => intro g; rfl
    | succ c ih => intro g; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hk]
  have hfold : ∀ (m : ι →₀ ℕ) (L : List ι),
      subst T (L.foldr (fun l g => (DofN F.F (cp l) (u l))^[m l] g) Φ) =
        L.foldr (fun l g => (pderiv l)^[m l] g) (subst T Φ : MvPowerSeries ι K) := by
    intro m L
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, hit, ih]
  unfold DpolyN derivAt0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, constantCoeff_C, mul_assoc, ← constantCoeff_subst_self T hT]
  congr 1
  unfold DmonN
  rw [hfold, ← coeff_zero_eq_constantCoeff_apply,
    ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_fold (fun l : ι => l) (fun _ _ h => h) m _ _ (Finset.nodup_toList _) 0,
    Finset.sum_map_toList, Finset.prod_map_toList]
  have h1 : (∑ l, m l • Finsupp.single l 1 : ι →₀ ℕ) = m := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.univ_sum_single m
  have h2 : (mfact m : K) = ∏ l, ((m l).factorial : K) := Finsupp.prod_fintype _ _ (by simp)
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.one_ascFactorial]
  rw [h1, h2, mul_comm]

end GlobalTheory.InvDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLOfCompactInvertibleMatrices
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem isCompact_GL_of_invSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Set (Lie E n)),
    IsCompact T → T ⊆ invSet E n →
      IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := by
  intro E _ _ n T hT hsub
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have hu : Continuous fun p : T =>
      (IsUnit.unit (hsub p.2 : IsUnit (Matrix.of p.1)) : GL (Fin n) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have hinv : ContDiffOn ℝ ∞ (GlobalTheory.ConstTermSmooth.invM (E := E) (a := n)) (invSet E n) := by
      have h1 : ContDiffOn ℝ ∞ (fun y : Lie E n => Ring.inverse (Matrix.of y).det) (invSet E n) := fun y hy => by
        obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hy
        have := contDiffAt_ringInverse ℝ (n := ∞) u
        rw [hu] at this
        exact (this.comp y contDiff_det.contDiffAt).contDiffWithinAt
      refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
      have h2 : ContDiff ℝ ∞ fun y : Lie E n => (Matrix.of y).adjugate i j := by
        simp only [Matrix.adjugate_apply]
        have h3 : ContDiff ℝ ∞ fun y : Lie E n => (Function.update y j (Pi.single i 1) : Lie E n) := by
          refine contDiff_pi.2 fun k => ?_
          by_cases h : k = j
          · subst h; simpa using contDiff_const
          · simpa [Function.update_of_ne h] using contDiff_apply ℝ _ k
        exact contDiff_det.comp h3
      exact h1.mul h2.contDiffOn
    have := hinv.continuousOn.comp_continuous
      (f := fun p : T => (p : Lie E n)) continuous_subtype_val fun p => hsub p.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  convert isCompact_range hu using 1
  ext y
  constructor
  · intro hy
    exact ⟨⟨toL (y : Matrix (Fin n) (Fin n) (Cinf E)), hy⟩, Units.ext rfl⟩
  · rintro ⟨p, rfl⟩
    exact p.2

end GlobalTheory.WhitBump
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
section
noncomputable section

open IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.AdicSpan

def IsIntB (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type} (b : Module.Basis κ ℚ M)
    (y : v.adicCompletion ℚ ⊗[ℚ] M) : Prop :=
  ∀ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ∈ v.adicCompletionIntegers ℚ

theorem isIntB_zero (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) : IsIntB v b 0 := fun i => by simp [zero_mem]

theorem isIntB_tmul_basis (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) (j : κ) : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b j) := fun i => by
  classical
  rw [Algebra.TensorProduct.basis_repr_tmul, b.repr_self, Finsupp.smul_apply, Finsupp.mapRange_apply,
    Finsupp.single_apply]
  split_ifs <;> simp [zero_mem, one_mem]

end GlobalTheory.AdicSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralLogHomDiagonalOfLimit
section
set_option autoImplicit false

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.DiagLimit

theorem isIntHom_diagonal_of_limit :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (G : LogFGL v d) (κ : Type) [Fintype κ] [DecidableEq κ] (U : Matrix (Fin d) κ C) (L : Matrix κ (Fin d) C), (∀ a b, IsIntV v (U a b)) → (∀ a b, IsIntV v (L a b)) → U * L = 1 → ∀ t : κ → C, (∀ r : ℝ, ∃ (t' : κ → C) (A : Matrix (Fin d) (Fin d) C) (φ : Fin d → MvPowerSeries (Fin d) C), IsIntHom G G φ A ∧ (∀ ℓ, A.mulVec (fun e => U e ℓ) = t' ℓ • fun e => U e ℓ) ∧ ∀ ℓ, (r : WithTop ℝ) ≤ v (t' ℓ - t ℓ)) → ∃ φ, IsIntHom G G φ (U * Matrix.diagonal t * L) := by
  intro C _ _ v d G κ _ _ U L hU hL hUL t h
  obtain ⟨φ, h1, h2, h3⟩ := GlobalTheory.IntegralEndLimit.integral_of_limit C v d G
    (U * Matrix.diagonal t * L) (fun r => by
      obtain ⟨t', A, φ, hφ, hA, ht⟩ := h r
      refine ⟨A, fun a b => ?_, φ, hφ.2.1, hφ.1, hφ.2.2⟩
      have e1 : A * U = U * Matrix.diagonal t' := by
        ext e ℓ
        have := congrFun (hA ℓ) e
        rw [Matrix.mul_diagonal, mul_comm]
        exact this
      have e2 : A = U * Matrix.diagonal t' * L := by
        rw [← e1, Matrix.mul_assoc, hUL, Matrix.mul_one]
      have e3 : (U * Matrix.diagonal t * L) a b - A a b =
          ∑ ℓ, U a ℓ * -(t' ℓ - t ℓ) * L ℓ b := by
        rw [e2, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
        ring
      rw [e3]
      refine v.map_le_sum fun ℓ _ => ?_
      rw [v.map_mul, v.map_mul, v.map_neg]
      have := add_le_add (add_le_add (show (0 : WithTop ℝ) ≤ v (U a ℓ) from hU a ℓ) (ht ℓ))
        (show (0 : WithTop ℝ) ≤ v (L ℓ b) from hL ℓ b)
      rwa [zero_add, add_zero] at this)
  exact ⟨φ, h2, h1, h3⟩

end GlobalTheory.DiagLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologySubsingletonStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n → Subsingleton (Ht q (sp B) n i) := by
  first | (exact @GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (exact GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (intros; apply GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le <;> assumption)
end

