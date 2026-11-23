module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0002
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsAlt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MapHaar
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_haar {nS nT N : ℕ} (α : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (hαc : Continuous α)
    (hαs : Continuous α.symm) (ν : Measure (WOF F E nS nT)) (hν : ν.IsAddHaarMeasure)
    (μN : Measure (Fin N → AF F)) (hμN : μN.IsAddHaarMeasure) :
    ∃ c : ℝ, 0 < c ∧ (∀ G : (Fin N → AF F) → ℂ, ∫ v, G (α v) ∂ν = (c : ℂ) * ∫ x, G x ∂μN) ∧
      ∀ G : (Fin N → AF F) → ℂ, Integrable (fun v => G (α v)) ν ↔ Integrable G μN := by
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI := hν
  haveI := hμN
  let a : WOF F E nS nT ≃ₜ (Fin N → AF F) :=
    { toEquiv := α.toEquiv, continuous_toFun := hαc, continuous_invFun := hαs }
  let m : WOF F E nS nT ≃ᵐ (Fin N → AF F) := a.toMeasurableEquiv
  have hm : ∀ v, m v = α v := fun _ => rfl
  haveI : ContinuousAdd (WOF F E nS nT) := ⟨by
    have h : (fun p : WOF F E nS nT × WOF F E nS nT => p.1 + p.2) = fun p => α.symm (α p.1 + α p.2) := by
      funext p; simp
    rw [h]
    exact hαs.comp ((hαc.comp continuous_fst).add (hαc.comp continuous_snd))⟩
  haveI : ContinuousNeg (WOF F E nS nT) := ⟨by
    have h : (fun x : WOF F E nS nT => -x) = fun x => α.symm (-α x) := by
      funext x; simp
    rw [h]
    exact hαs.comp hαc.neg⟩
  haveI hmap : (Measure.map α ν).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map ν α.toAddEquiv hαc hαs
  have hmm : Measure.map m ν = Measure.map α ν := rfl
  set c := Measure.addHaarScalarFactor (Measure.map α ν) μN with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have heq : Measure.map α ν = c • μN := by
    first
    | exact Measure.isAddHaarMeasure_eq_smul _ _
    | exact Measure.isAddLeftInvariant_eq_smul _ _
    | exact Measure.isAddLeftInvariant_eq_smul_of_regular _ _
  have heq' : Measure.map α ν = (c : ENNReal) • μN := by
    rw [heq]
    rfl
  refine ⟨c, hc, fun G => ?_, fun G => ?_⟩
  · have h1 : ∫ v, G (α v) ∂ν = ∫ x, G x ∂(Measure.map m ν) := (integral_map_equiv m G).symm
    rw [h1, hmm, heq', integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]
  · have h1 : Integrable (fun v => G (α v)) ν ↔ Integrable G (Measure.map m ν) :=
      (integrable_map_equiv m G).symm
    rw [h1, hmm, heq']
    exact integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.RowsStackRight
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem exists_nsmul_mem {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (h : L.IsFullLattice E) (v : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • v ∈ L := by
  letI := h
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [Submodule.IsFullLattice.span_eq_top]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
  rw [Submodule.span_eq] at ht
  have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero t.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)}))
  refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero fun h0 => ht0 ?_, ?_⟩
  · exact Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h0)
  · rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul]
    exact L.smul_mem c ht

theorem trace_int_iff (z : E) : (∃ n : ℤ, Algebra.trace ℚ E z = n) ↔ IsIntegral ℤ (Algebra.trace ℚ E z) := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨n, h⟩ => ⟨n, h.symm⟩, fun ⟨n, h⟩ => ⟨n, h.symm⟩⟩

section Tensor

variable {n d : ℕ}

def ctr (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (t : Fin n → E) :
    Matrix (Fin n) (Fin d) E →ₗ[𝓞 E] (Fin d → E) where
  toFun M := fun a => ∑ j, M j a * ∑ k, σ (t k) * J j k
  map_add' M M' := by
    funext a
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    funext a
    simp [Algebra.smul_def, Finset.mul_sum, mul_assoc]

def ten (t : Fin n → E) : (Fin d → E) →ₗ[𝓞 E] Matrix (Fin n) (Fin d) E where
  toFun s := Matrix.of fun j a => t j * s a
  map_add' s s' := by
    ext j a
    simp [mul_add]
  map_smul' c s := by
    ext j a
    simp [Algebra.smul_def, mul_left_comm]

theorem ctr_ten (J : Matrix (Fin n) (Fin n) E) (t t' : Fin n → E) (s : Fin d → E) :
    ctr σ J t' (ten t s) = form σ J t t' • s := by
  funext a
  simp only [ctr, ten, form, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hRat_ten (JX : Matrix (Fin n) (Fin n) E) (JW JS : Matrix (Fin d) (Fin d) E) (ξ₀ : E) (h : ξ₀ • JS⁻¹ = -JW)
    (M : Matrix (Fin n) (Fin d) E) (t : Fin n → E) (s : Fin d → E) :
    ξ₀ * hRatF σ JS JXᵀ M (ten t s) = -form σ JW (ctr σ JX t M) s := by
  have e : ∀ a b, ξ₀ * JS⁻¹ a b = -JW a b := fun a b => congrFun (congrFun h a) b
  simp only [hRatF, ctr, ten, form, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply, map_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  linear_combination (σ (t k) * σ (s b) * JX j k * M j a) * e a b

theorem hRat_sum {ι : Type} [Fintype ι] (JT : Matrix (Fin n) (Fin n) E) (JS : Matrix (Fin d) (Fin d) E)
    (M : Matrix (Fin n) (Fin d) E) (N : ι → Matrix (Fin n) (Fin d) E) :
    hRatF σ JS JT M (∑ i, N i) = ∑ i, hRatF σ JS JT M (N i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hRatF]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp only [hRatF, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem latH_of {B : Base F E} (hcm : IsCMExt F E σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} {ξ₀ : E}
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hXu : IsUnit X.J.det) (hWu : IsUnit W.J.det) (hξ : ξ₀ ≠ 0) :
    LatH σ (-ξ₀ • W.J⁻¹) X.Jᵀ ξ₀ := by
  have e1 : (-ξ₀ • W.J⁻¹)⁻¹ = (-ξ₀)⁻¹ • W.J := Matrix.inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hWu,
      inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
  have e2 : ξ₀ • (-ξ₀ • W.J⁻¹)⁻¹ = -W.J := by
    rw [e1, smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
  letI : StarRing E :=
    { star := σ
      star_involutive := sig_sig hcm
      star_mul := fun a b => by show σ (a * b) = σ b * σ a; rw [map_mul, mul_comm]
      star_add := fun a b => map_add σ a b }
  obtain ⟨m, u, u', hu, hd⟩ := GlobalTheory.LatVacDual.exists_dual_family X.Jᵀ (fun i j => hX.herm i j)
    (by rwa [Matrix.det_transpose]) X.L hX.lat.fg (by letI := hX.lat; exact Submodule.IsFullLattice.span_eq_top) (fun y hy => (hX.dual y).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy x hx
      have : form σ X.J y x = b := by
        rw [hb, Finset.sum_comm]
        simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
        show _ = σ _ * _ * _
        ring
      rw [this]
      exact b.2)
  have key : ∀ M : Matrix (Fin n) (Fin d) E, M = ∑ i, ten (u i) (ctr σ X.J (u' i) M) := fun M => by
    ext j a
    have : ∀ l, ∑ i, u i j * ∑ k, σ (u' i k) * X.J l k = if j = l then 1 else 0 := fun l => hd j l
    calc M j a = ∑ l, M l a * ∑ i, u i j * ∑ k, σ (u' i k) * X.J l k := by simp [this]
      _ = _ := by
        rw [Matrix.sum_apply]
        simp only [ten, ctr, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
        simp only [Finset.mul_sum (s := (Finset.univ : Finset (Fin m)))]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _
  let Λ : Submodule (𝓞 E) (Matrix (Fin n) (Fin d) E) := ⨅ t ∈ X.L, W.L.comap (ctr σ X.J t)
  have hΛ : ∀ M, M ∈ Λ ↔ ∀ t ∈ X.L, ctr σ X.J t M ∈ W.L := fun M => by simp [Λ, Submodule.mem_iInf]
  have hten : ∀ t ∈ X.L, ∀ s ∈ W.L, ten t s ∈ Λ := fun t ht s hs => (hΛ _).2 fun t' ht' => by
    rw [ctr_ten]
    exact W.L.smul_mem (⟨_, (hX.dual t).1 ht t' ht'⟩ : 𝓞 E) hs
  refine ⟨Λ, ⟨?_, fun M => ?_⟩, fun M => ⟨fun hM M' hM' => ?_, fun H => (hΛ _).2 fun t ht => (hW.dual _).2 fun x hx o => ?_⟩⟩
  · have : Λ = ⨆ i, W.L.map (ten (u i)) := le_antisymm (fun M hM => by
      rw [key M]
      exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, (hΛ M).1 hM _ (hu i).2, rfl⟩)
      (iSup_le fun i => by
        rintro _ ⟨x, hx, rfl⟩
        exact hten _ (hu i).1 x hx)
    rw [this]
    exact Submodule.fg_iSup _ fun i => hW.lat.fg.map _
  · choose N hN hN' using fun i => exists_nsmul_mem hW.lat (ctr σ X.J (u' i) M)
    refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, ?_⟩
    rw [key M, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
    rw [← map_nsmul, hc, mul_comm, mul_smul]
    exact hten _ (hu i).1 _ (nsmul_mem (hN' i) c)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [trace_int_iff, key M', hRat_sum, Finset.mul_sum, map_sum]
      refine IsIntegral.sum _ fun i _ => ?_
      rw [hRat_ten X.J W.J _ ξ₀ e2, map_neg]
      have := (hW.dual _).1 ((hΛ M).1 hM _ (hu i).1) _ ((hΛ M').1 hM' _ (hu i).2) 1
      simpa using this.neg
  · let o' : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) o
    have h1 := (trace_int_iff _).1 (H _ (hten t ht _ (W.L.smul_mem o' hx)))
    rw [hRat_ten X.J W.J _ ξ₀ e2, map_neg] at h1
    have h2 : form σ W.J (ctr σ X.J t M) (o' • x) = o * form σ W.J (ctr σ X.J t M) x := by
      have : ∀ i, σ ((o' • x) i) = o * σ (x i) := fun i => by
        show σ (σ o * x i) = _
        rw [map_mul, sig_sig hcm]
      simp only [form, this, dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h2] at h1
    simpa using h1.neg

end Tensor

section Dbl

variable {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

def rowsL {m : ℕ} (f : Fin nT → Fin m) : Matrix (Fin m) (Fin nS) E →ₗ[𝓞 E] Matrix (Fin nT) (Fin nS) E where
  toFun M := M.submatrix f id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def stackL : (Matrix (Fin nT) (Fin nS) E × Matrix (Fin nT) (Fin nS) E) →ₗ[𝓞 E] Matrix (Fin (nT + nT)) (Fin nS) E where
  toFun p := Matrix.of fun i j => Fin.append (fun k => p.1 k j) (fun k => p.2 k j) i
  map_add' p q := by
    ext i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [-Fin.natAdd_eq_addNat]
  map_smul' c p := by
    ext i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [-Fin.natAdd_eq_addNat]

theorem rowsL_apply {m : ℕ} (f : Fin nT → Fin m) (M : Matrix (Fin m) (Fin nS) E) (i j) : rowsL f M i j = M (f i) j := rfl

theorem stackL_apply (p : Matrix (Fin nT) (Fin nS) E × Matrix (Fin nT) (Fin nS) E) (i j) :
    stackL p i j = Fin.append (fun k => p.1 k j) (fun k => p.2 k j) i := rfl

theorem rows_stack_left (p : Matrix (Fin nT) (Fin nS) E × Matrix (Fin nT) (Fin nS) E) :
    rowsL (Fin.castAdd nT) (stackL p) = p.1 := by
  ext i j
  simp [rowsL_apply, stackL_apply]

theorem rows_stack_right (p : Matrix (Fin nT) (Fin nS) E × Matrix (Fin nT) (Fin nS) E) :
    rowsL (Fin.natAdd nT) (stackL p) = p.2 := by
  ext i j
  simp [rowsL_apply, stackL_apply, -Fin.natAdd_eq_addNat]

theorem stack_rows (M : Matrix (Fin (nT + nT)) (Fin nS) E) :
    stackL (rowsL (Fin.castAdd nT) M, rowsL (Fin.natAdd nT) M) = M := by
  ext i j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [rowsL_apply, stackL_apply, -Fin.natAdd_eq_addNat]

theorem hRat_dbl (x y : Matrix (Fin (nT + nT)) (Fin nS) E) :
    hRatF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) x y =
      hRatF σ JS JT (rowsL (Fin.castAdd nT) x) (rowsL (Fin.castAdd nT) y) -
        hRatF σ JS JT (rowsL (Fin.natAdd nT) x) (rowsL (Fin.natAdd nT) y) := by
  simp [hRatF, rowsL_apply, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, Fin.sum_univ_add, sub_eq_add_neg, Finset.sum_add_distrib,
    -Fin.natAdd_eq_addNat]

theorem hRat_zero_right (x : Matrix (Fin nT) (Fin nS) E) : hRatF σ JS JT x 0 = 0 := by simp [hRatF]

theorem LatH.dblT (h : LatH σ JS JT ξ₀) : LatH σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ := by
  obtain ⟨Λ, ⟨h1, h2⟩, h3⟩ := h
  have hm : ∀ M, M ∈ (Λ.prod Λ).map stackL ↔ rowsL (Fin.castAdd nT) M ∈ Λ ∧ rowsL (Fin.natAdd nT) M ∈ Λ := fun M =>
    ⟨by
      rintro ⟨p, hp, rfl⟩
      rw [rows_stack_left, rows_stack_right]
      exact hp, fun H => ⟨(_, _), H, stack_rows M⟩⟩
  refine ⟨(Λ.prod Λ).map stackL, ⟨(h1.prod h1).map _, fun M => ?_⟩, fun M => ⟨fun hM M' hM' => ?_, fun H => (hm _).2 ⟨?_, ?_⟩⟩⟩
  · obtain ⟨N, hN, a⟩ := h2 (rowsL (Fin.castAdd nT) M)
    obtain ⟨N', hN', b⟩ := h2 (rowsL (Fin.natAdd nT) M)
    refine ⟨N * N', Nat.mul_pos hN hN', (hm _).2 ⟨?_, ?_⟩⟩
    · rw [map_nsmul, mul_comm, mul_smul]
      exact nsmul_mem a _
    · rw [map_nsmul, mul_smul]
      exact nsmul_mem b _
  · obtain ⟨a, ha⟩ := (h3 _).1 ((hm _).1 hM).1 _ ((hm _).1 hM').1
    obtain ⟨b, hb⟩ := (h3 _).1 ((hm _).1 hM).2 _ ((hm _).1 hM').2
    exact ⟨a - b, by rw [hRat_dbl, mul_sub, map_sub, ha, hb, Int.cast_sub]⟩
  · refine (h3 _).2 fun M' hM' => ?_
    obtain ⟨a, ha⟩ := H (stackL (M', 0)) ⟨_, ⟨hM', Λ.zero_mem⟩, rfl⟩
    rw [hRat_dbl, rows_stack_left, rows_stack_right, hRat_zero_right, sub_zero] at ha
    exact ⟨a, ha⟩
  · refine (h3 _).2 fun M' hM' => ?_
    obtain ⟨a, ha⟩ := H (stackL (0, M')) ⟨_, ⟨Λ.zero_mem, hM'⟩, rfl⟩
    rw [hRat_dbl, rows_stack_left, rows_stack_right, hRat_zero_right, zero_sub, mul_neg, map_neg] at ha
    exact ⟨-a, by rw [Int.cast_neg, ← ha, neg_neg]⟩

end Dbl

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SetIntegralAddRight
section
open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

section aux
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hOF_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (a b : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (dC F E nT * a) (dC F E nT * b) = 0 := by
  have ha : dC F E nT * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    GlobalTheory.LagrThetaInv.dC_mul_eq a
  have hb : dC F E nT * b = Matrix.of fun i j => b (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    GlobalTheory.LagrThetaInv.dC_mul_eq b
  rw [ha, hb]
  unfold hOF
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, GlobalTheory.LagrThetaInv.dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem symplOHF_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (a b : WOF F E nS nT) :
    symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dC F E nT * a) (dC F E nT * b) = 0 := by
  simp only [symplOHF, symplOF, hOF_dC, mul_zero, map_zero]

theorem dC_mul_ratWF {nS nT : ℕ} (γ : Matrix (Fin nT) (Fin nS) E) :
    (dC F E nT * (ratWF γ : WOF F E nS nT) : WOF F E nS (nT + nT)) = ratWF (GlobalTheory.LagrThetaInv.dC E nT * γ) :=
  GlobalTheory.LagrThetaInv.dC_mul_rat γ

theorem setIntegral_add_right {nS nT : ℕ} (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    [ν.IsAddHaarMeasure] (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (g : WOF F E nS nT → ℂ)
    (h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v) (u : WOF F E nS nT) :
    ∫ v in 𝓕, g (v + u) ∂ν = ∫ v in 𝓕, g v ∂ν := by
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  haveI : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  haveI : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  haveI : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  haveI : Countable (ratLF F E nS nT) := by
    haveI : Countable E := by
      haveI : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1
      funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2

end aux

theorem lagrInt_heis_dC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f → ∀ v : WOF F E nS nT,
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT)
                     (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC F E nT * v) f) =
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ ν 𝓕 _ h𝓕 f hf u
  set g : WOF F E nS nT → ℂ := fun v => f (dC F E nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC F E nT * u) f
      (dC F E nT * v) = g (v + u) := by
    intro v
    simp only [hg, heisOF]
    rw [symplOHF_dC, AddChar.map_zero_eq_one, one_mul, Matrix.mul_add]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    show f (dC F E nT * ((ratWF γ : WOF F E nS nT) + v)) = f (dC F E nT * v)
    have hq := hf.quasi (GlobalTheory.LagrThetaInv.dC E nT * γ) (dC F E nT * v)
    rw [← dC_mul_ratWF, symplOHF_dC, neg_zero, AddChar.map_zero_eq_one, one_mul] at hq
    rw [Matrix.mul_add, hq]
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [h1]
  exact setIntegral_add_right ν 𝓕 h𝓕 g h2 u

end GlobalTheory.SplitLagrF

end
end

