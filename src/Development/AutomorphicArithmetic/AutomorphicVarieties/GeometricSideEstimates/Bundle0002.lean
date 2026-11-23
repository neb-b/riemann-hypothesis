module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
public import GroundTheory.GlobalFields.Adele.Topology

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HeightBoundOfQuasiHeightLe
section
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem ratio_bound {m : ℕ} {f : Fin (m + 1) → ℝ} {c u : ℝ} (hf : ∀ i, 0 < f i) (hc : 0 ≤ c)
    (hu : ∀ i, f i ≤ u) (h1 : 1 ≤ c * ∏ i, f i) (i j : Fin (m + 1)) : f i / f j ≤ c * u ^ (m + 1) := by
  rw [Fin.prod_univ_succAbove _ j] at h1
  have h2 : ∏ k, f (j.succAbove k) ≤ u ^ m := by
    calc ∏ k, f (j.succAbove k) ≤ ∏ _k : Fin m, u := Finset.prod_le_prod₀ (fun k _ => (hf _).le) fun k _ => hu _
      _ = u ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hu0 : 0 < u := (hf i).trans_le (hu i)
  have h3 : 1 ≤ c * (f j * u ^ m) :=
    h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (hf j).le) hc)
  rw [div_le_iff₀ (hf j)]
  calc f i ≤ u * 1 := by rw [mul_one]; exact hu i
    _ ≤ u * (c * (f j * u ^ m)) := mul_le_mul_of_nonneg_left h3 hu0.le
    _ = c * u ^ (m + 1) * f j := by ring

private theorem chain_first {m : ℕ} {r : Fin (m + 1) → ℝ} {t s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hst : s ≤ t) (hr : ∀ i, 0 < r i) (h : ∀ i j : Fin (m + 1), (j : ℕ) = i + 1 → t * r j ≤ r i)
    (i : Fin (m + 1)) : s ^ m * r i ≤ r 0 := by
  have h1 := Reduction.pow_mul_le_of_chain (r := fun j => (r j.rev)⁻¹) hs0 hs1 hst (fun j => inv_pos.2 (hr _))
    (fun p q hpq => by
      have h2 := h q.rev p.rev (by have := q.2; simp only [Fin.val_rev]; omega)
      rw [← div_eq_mul_inv, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ (hr _)]
      exact h2) i.rev
  simp only [Fin.rev_last, Fin.rev_rev] at h1
  rw [← div_eq_mul_inv, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ (hr _)] at h1
  exact h1

private theorem le_of_pow_le {x c : ℝ} {d : ℕ} (hd : d ≠ 0) (hc : 1 ≤ c) (h : x ^ d ≤ c) : x ≤ c := by
  rcases le_or_gt x 1 with h1 | h1
  · exact h1.trans hc
  · exact (le_self_pow₀ h1.le hd).trans h

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem qht_le_height (g : KernelIndexFullLattice.G1 E a) (γ : GL (Fin a) E) :
    qht (E := E) (a := a) g.1 ≤ height (AdelicGLn.diagonal E a γ * g.1) := by
  have h1 := ciInf_le (f := fun γ : GL (Fin a) E =>
    height (K := E) (ratGL E a γ * (retractOne g.1 : KernelIndexFullLattice.G1 E a).1))
    ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩ γ
  rw [retractOne_coe] at h1
  unfold qht
  rw [retractOne_coe]
  exact h1

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem prod_bound {ω : Set (AdelicGLn.AdelicGL E a)} (hω : IsCompact ω) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL E a)),
      b * Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) * kk ∈ Reduction.normOneGL (K := E) (n := a) →
      ∏ i, ρ i ≤ c ∧ (∏ i, ρ i)⁻¹ ≤ c := by
  have hdc : Continuous fun g : AdelicGLn.AdelicGL E a => (Reduction.detModule E a g : ℝ) :=
    continuous_subtype_val.comp Reduction.continuous_detModule
  obtain ⟨M₁, hM₁⟩ := hω.bddAbove_image hdc.continuousOn
  obtain ⟨M₂, hM₂⟩ := hω.bddAbove_image (hdc.inv₀ fun g => (Reduction.detModule E a g).2.ne').continuousOn
  refine ⟨max 1 (max M₁ M₂), le_max_left _ _, fun b hb ρ hρ kk hkk hx => ?_⟩
  have hd : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  have h1 := Reduction.mem_normOneGL_iff_detModule.1 hx
  rw [map_mul, map_mul, Reduction.mem_normOneGL_iff_detModule.1 (Reduction.maxCompact_le_normOneGL hkk),
    mul_one] at h1
  have h2 := congrArg Subtype.val h1
  rw [Positive.val_mul, detModule_diagUnits_posIdele, Positive.val_one] at h2
  have h3 := eq_inv_of_mul_eq_one_right h2
  constructor
  · refine le_of_pow_le hd (le_max_left _ _) ?_
    rw [h3]
    exact (hM₂ ⟨b, hb, rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))
  · refine le_of_pow_le hd (le_max_left _ _) ?_
    rw [inv_pow, h3, inv_inv]
    exact (hM₁ ⟨b, hb, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))

end

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.height_bound_of_quasiHeight_le :
    SiegelHt := by
  intro E _ _ _ a
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) a
  rcases a with _ | m
  · refine ⟨ω, 0, 0, hω, hωB, fun g => ?_⟩
    obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
    exact ⟨γ, b, kk, ρ, hρ, hb, hkk, hxe, fun i => i.elim0⟩
  obtain ⟨Ch, hCh0, hCh⟩ := exists_height_le_normOne (K := E) (n := m + 1) hω
  obtain ⟨c, hc, hcb⟩ := prod_bound hω
  have hc0 : 0 < c := one_pos.trans_le hc
  have hs0 : 0 < min t 1 := lt_min ht one_pos
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = (min t 1) ^ m := ⟨_, rfl⟩
  have hσ0 : 0 < σ := hσ ▸ pow_pos hs0 m
  obtain ⟨e, he⟩ : ∃ e, e = Fintype.card (InfinitePlace E) := ⟨_, rfl⟩
  rw [← he] at hCh
  refine ⟨ω, Ch * c ^ (2 * e) * σ⁻¹ ^ (2 * ((m + 1) * e)), (m + 1) * e, hω, hωB, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγx : AdelicGLn.diagonal E (m + 1) γ * g.1 ∈ Reduction.normOneGL (K := E) (n := (m + 1)) :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) g.2
  obtain ⟨hP1, hP2⟩ := hcb b hb ρ hρ kk hkk (hxe ▸ hγx)
  have hP : 0 < ∏ i, ρ i := Finset.prod_pos fun i _ => hρ i
  have key : ∀ v : ℝ, (∀ i j, ρ i / ρ j ≤ c * (σ⁻¹ * v) ^ (m + 1)) →
      qht (E := E) (a := m + 1) g.1 ≤ Ch * c ^ (2 * e) * σ⁻¹ ^ (2 * ((m + 1) * e)) * v ^ (2 * ((m + 1) * e)) := by
    intro v hv
    have h1 : 1 ≤ c * (σ⁻¹ * v) ^ (m + 1) := by
      have := hv 0 0
      rwa [div_self (hρ 0).ne'] at this
    refine (qht_le_height g γ).trans ((hCh b hb ρ hρ kk hkk _ hγx hxe _ h1 hv).trans_eq ?_)
    simp only [mul_pow, ← pow_mul]
    rw [show (m + 1) * (2 * e) = 2 * ((m + 1) * e) by ring]
    ring
  refine ⟨γ, b, kk, ρ, hρ, hb, hkk, hxe, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl : i = Fin.last m := Fin.ext (by simpa using hi)
    have h := key (ρ (Fin.last m))⁻¹ fun p q => by
      have h1 := ratio_bound (f := fun j => (ρ j)⁻¹) (u := σ⁻¹ * (ρ (Fin.last m))⁻¹) (fun j => inv_pos.2 (hρ j)) hc0.le
        (fun j => by
          rw [← mul_inv]
          refine inv_anti₀ (mul_pos hσ0 (hρ _)) ?_
          rw [hσ]
          exact Reduction.pow_mul_le_of_chain hs0.le (min_le_right _ _) (min_le_left _ _) hρ hs j)
        (by rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, one_le_div hP]; exact hP1) q p
      rwa [inv_div_inv] at h1
    rwa [inv_pow (ρ _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos (hρ _) _)] at h
  · obtain rfl : i = 0 := Fin.ext hi
    refine key (ρ 0) fun p q => ratio_bound hρ hc0.le (fun j => ?_) ?_ p q
    · rw [le_inv_mul_iff₀ hσ0, hσ]
      exact chain_first hs0.le (min_le_right _ _) (min_le_left _ _) hρ hs j
    · rwa [inv_le_iff_one_le_mul₀ hP] at hP2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.LieDerivativeIsDerivationSmoothFunctions
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_prod (f f' : GA E a → ℂ) (g : GA E a) :
    chart (f * f') g = chart f g * chart f' g := by
  funext x
  simp only [Pi.mul_apply, chart]
  split_ifs <;> simp

private theorem sm_prod_mem {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) : f * f' ∈ Sm E a := by
  intro g
  rw [chart_prod]
  exact (h g).mul (h' g)

private theorem leibniz (X : Lie E a) {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) :
    lieD X (f * f') = f * lieD X f' + lieD X f * f' := by
  funext g
  have v : ∀ u : GA E a → ℂ, chart u g (oneL E a) = u g := fun u => by
    simpa using chart_val u g 1
  simp only [lieD, Pi.add_apply, Pi.mul_apply]
  rw [chart_prod, fderiv_mul (differentiableAt_chart h g) (differentiableAt_chart h' g), v, v]
  simp [mul_comm]

private theorem const_ev (c : ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (algebraMap ℂ (GA E a → ℂ) c) g x = c := by
  unfold chart
  rw [dite_eq_left (show IsUnit (Matrix.of x) from hx)]
  rfl

private theorem const_mem (c : ℂ) : algebraMap ℂ (GA E a → ℂ) c ∈ Sm E a := fun g =>
  contDiffOn_const.congr fun _ hx => const_ev c g hx

private theorem lie_const (X : Lie E a) (c : ℂ) : lieD X (algebraMap ℂ (GA E a → ℂ) c) = 0 := by
  funext g
  have e : chart (algebraMap ℂ (GA E a → ℂ) c) g =ᶠ[nhds (oneL E a)] fun _ => c := by
    have h1 : oneL E a ∈ invSet E a := isUnit_one
    filter_upwards [isOpen_invSet.mem_nhds h1] with x hx using const_ev c g hx
  rw [lieD, e.fderiv_eq]
  simp

end

theorem UpperTheory.lieDerivative_isDerivation_smoothFunctions :
    BddAlg := by
  intro E _ _ _ a S hS
  have key : ∀ f ∈ Algebra.adjoin ℂ S, (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ f ∈ Sm E a ∧
      ∀ X : Lie E a, lieD X f ∈ Algebra.adjoin ℂ S := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨hb, φ, rfl, hX⟩ := hS f hf
      exact ⟨hb, φ.2, hX⟩
    | algebraMap c =>
      exact ⟨⟨‖c‖, fun g => by simp⟩, const_mem c, fun X => by rw [lie_const]; exact zero_mem _⟩
    | add f f' _ _ h h' =>
      obtain ⟨⟨C, hC⟩, hs, hX⟩ := h
      obtain ⟨⟨C', hC'⟩, hs', hX'⟩ := h'
      refine ⟨⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩, add_mem hs hs', fun X => ?_⟩
      have e : lieD X (f + f') = lieD X f + lieD X f' :=
        congrArg Subtype.val ((lie E a X).map_add (⟨f, hs⟩ : Sm E a) (⟨f', hs'⟩ : Sm E a))
      rw [e]
      exact add_mem (hX X) (hX' X)
    | mul f f' hf hf' h h' =>
      obtain ⟨⟨C, hC⟩, hs, hX⟩ := h
      obtain ⟨⟨C', hC'⟩, hs', hX'⟩ := h'
      refine ⟨⟨C * C', fun g => (norm_mul_le _ _).trans
        (mul_le_mul (hC g) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC g)))⟩, sm_prod_mem hs hs', fun X => ?_⟩
      rw [leibniz X hs hs']
      exact add_mem (mul_mem hf (hX' X)) (mul_mem (hX X) hf')
  have main : ∀ ψ : Sm E a, (∀ X, (lie E a X ψ).1 ∈ Algebra.adjoin ℂ S) → BddDer ψ := by
    intro ψ hψ
    have h : ∀ (l : List (Lie E a)) (X : Lie E a),
        (((X :: l).map (lie E a)).prod ψ).1 ∈ Algebra.adjoin ℂ S := by
      intro l
      induction l with
      | nil => intro X; simpa using hψ X
      | cons Y l ih =>
        intro X
        rw [List.map_cons, List.prod_cons]
        exact (key _ (ih Y)).2.2 X
    exact fun X l => (key _ (h l X)).1
  exact ⟨fun f hf => ⟨⟨f, (key f hf).2.1⟩, rfl, main _ (key f hf).2.2⟩, main⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments
section
open UpperTheory.V.Lit.Geo

private theorem moment_pt (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ k * Real.exp (-Real.pi * x) ≤
      (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * x)) := by
  have h1 : (1 + x) ^ k / (k.factorial : ℝ) ≤ Real.exp (1 + x) :=
    Real.pow_div_factorial_le_exp (1 + x) (by linarith) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h2 : (1 + x) ^ k ≤ k.factorial * Real.exp (1 + x) := by
    rw [div_le_iff₀ hf] at h1
    linarith
  calc (1 + x) ^ k * Real.exp (-Real.pi * x)
      ≤ k.factorial * Real.exp (1 + x) * Real.exp (-Real.pi * x) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (k.factorial * Real.exp 1) * Real.exp (x + -Real.pi * x) := by
        rw [Real.exp_add, Real.exp_add]
        ring
    _ ≤ (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.2
        nlinarith [Real.pi_gt_three]

theorem UpperTheory.moment_bound_of_pointwise_moments :
    Moment := by
  intro N k
  refine ⟨k.factorial * Real.exp 1 * 2 ^ N, by positivity, fun ι q hq => ?_⟩
  obtain ⟨hs1, hle⟩ := hq.2 (1 / 2) 1 (by norm_num) (by norm_num)
  have hnn : ∀ i, 0 ≤ (1 + q i) ^ k * Real.exp (-Real.pi * q i) := fun i => by
    have := hq.1 i
    positivity
  have hpt : ∀ i, (1 + q i) ^ k * Real.exp (-Real.pi * q i) ≤
      (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * q i)) := fun i => moment_pt k (q i) (hq.1 i)
  have hsum : Summable fun i => (1 + q i) ^ k * Real.exp (-Real.pi * q i) :=
    Summable.of_nonneg_of_le hnn hpt (hs1.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' i, (1 + q i) ^ k * Real.exp (-Real.pi * q i)
      ≤ ∑' i, (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * q i)) :=
        hsum.tsum_le_tsum hpt (hs1.mul_left _)
    _ = (k.factorial * Real.exp 1) * ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) := tsum_mul_left
    _ ≤ (k.factorial * Real.exp 1) * ((1 / (1 / 2)) ^ N * ∑' i, Real.exp (-Real.pi * (1 * q i))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = k.factorial * Real.exp 1 * 2 ^ N * ∑' i, Real.exp (-Real.pi * q i) := by
        rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num]
        simp only [one_mul]
        ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RationalPointRetractionExistsCmDatum
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem hom_one {G : Type} [Group G] [TopologicalSpace G] (U : Subgroup G) (hU : IsCompact (U : Set G))
    (φ : G →* {r : ℝ // 0 < r}) (hc : Continuous φ) : ∀ u ∈ U, φ u = 1 := by
  obtain ⟨m, hmU, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hc.continuousOn
  have hle : ∀ u ∈ U, φ u ≤ 1 := fun u hu => by
    have h : φ (u * m) ≤ φ m := hmax (U.mul_mem hu hmU)
    rw [map_mul, mul_comm] at h
    exact (mul_le_iff_le_one_right' _).1 h
  intro u hu
  have h2 := hle _ (U.inv_mem hu)
  rw [map_inv, inv_le_one'] at h2
  exact le_antisymm (hle u hu) h2

private theorem ptF_rat (γ : GL (Fin a) E) (g : GA E a) (v : Fin a → E) :
    ptF (ratGL E a γ * g) v = ptF g (v ᵥ* γ.val) := by
  have h : vFin (v ᵥ* γ.val) = vFin v ᵥ* (GeneralLinearGroup.map (pFin E) (ratGL E a γ)).val :=
    funext fun j => RingHom.map_vecMul (algebraMap E (Af E)) γ.val v j
  change vFin v ᵥ* _ = vFin (v ᵥ* γ.val) ᵥ* _
  rw [h, map_mul, Units.val_mul, Matrix.vecMul_vecMul]

variable [_root_.NumberField.IsTotallyComplex E]

private theorem pt_rat (γ : GL (Fin a) E) (g : GA E a) (v : Fin a → E) :
    pt (ratGL E a γ * g) v = pt g (v ᵥ* γ.val) := by
  have h : vInf (v ᵥ* γ.val) = vInf v ᵥ* (GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val :=
    funext fun j => RingHom.map_vecMul ((pInf E).comp (algebraMap E (Ad E))) γ.val v j
  change vInf v ᵥ* _ = vInf (v ᵥ* γ.val) ᵥ* _
  rw [h, map_mul, Units.val_mul, Matrix.vecMul_vecMul]

private theorem rt_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    rt (ratGL E a γ * splitCentre E a t * g) = ratGL E a γ * rt g := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem retract_rt (g : GA E a) : retractOne (rt g) = retractOne g := retractOne_coe _

private theorem ptF_rt (g : GA E a) : ptF (rt g) = ptF g := by
  have h : GeneralLinearGroup.map (pFin E) (rt g) = GeneralLinearGroup.map (pFin E) g := finPart_retract g
  refine AddMonoidHom.ext fun v => ?_
  change vFin v ᵥ* _ = vFin v ᵥ* _
  rw [h]

private theorem rt_fin (U : Subgroup (GL (Fin a) (Af E))) (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    (u : GL (Fin a) (Af E)) (hu : u ∈ U) (g : GA E a) : rt (g * finGL E a u) = rt g * finGL E a u := by
  have h1 : Reduction.detModule E a (finGL E a u) = 1 := by
    rw [← Fb.finEmb_eq]
    exact hom_one U hU ((Reduction.detModule E a).comp (finEmb E a))
      (Reduction.continuous_detModule.comp continuous_finEmb) u hu
  unfold Lit.Geo.rt
  rw [coe_retractOne, coe_retractOne, map_mul, h1, mul_one, mul_assoc, ← centralSection_inv_mul_comm, ← mul_assoc]

end

theorem UpperTheory.rationalPoint_retraction_exists_cmDatum :
    RtFacts := by
  intro E _ _ _ a _
  refine ⟨rt_left, fun g => ⟨congrArg Subtype.val (retract_rt g), ?_, ptF_rt g⟩,
    fun γ g v => ⟨ptF_rat γ g v, pt_rat γ g v⟩, rt_fin⟩
  unfold qht
  rw [retract_rt]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TraceFormCauchySchwarzCmDatum
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private lemma re_mul_conj (z : ℂ) : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private lemma sum_mul_le {ι : Type} [Fintype ι] (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, f i * g i ≤ (∑ i, f i) * ∑ i, g i := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => hg j) (Finset.mem_univ i)) (hf i)

private lemma cs_norm {ι : Type} [Fintype ι] (f g : ι → ℂ) :
    ‖∑ i, f i * g i‖ ^ 2 ≤ (∑ i, ‖f i‖ ^ 2) * ∑ i, ‖g i‖ ^ 2 := by
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖f i‖) (fun i => ‖g i‖))
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private lemma qf_eq (w : Fin a → Cinf E) : qf w = ∑ v : InfinitePlace E, ∑ i, ‖w i v‖ ^ 2 := by
  unfold qf; exact Finset.sum_comm

private lemma trF_eq (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF X Y = (∑ p : InfinitePlace E × Fin a × Fin a, X p.2.1 p.2.2 p.1 * Y p.2.2 p.2.1 p.1).re := by
  simp [trF, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_apply]

private lemma quad_eq (w x : Fin a → Cinf E) :
    quad (vecMulVec w (star w)) x = ∑ v : InfinitePlace E, ‖(x ⬝ᵥ w) v‖ ^ 2 := by
  unfold quad
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.vecMul_vecMulVec, smul_dotProduct, ← re_mul_conj]
  congr 1
  simp [dotProduct, Finset.sum_apply, mul_comm]

end

theorem UpperTheory.traceForm_cauchy_schwarz_cmDatum :
    RankOne := by
  intro E _ _ a w
  refine ⟨?_, fun M => ?_, fun x => ⟨?_, ?_, fun h => ?_⟩⟩
  · rw [qf_eq]
    unfold trF
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Matrix.one_mul, Matrix.trace, Matrix.diag, vecMulVec_apply, Finset.sum_apply, Complex.re_sum,
      Pi.mul_apply, Pi.star_apply, Complex.star_def, re_mul_conj]
  · have hM : ∀ i j v, M.1 j i v = (starRingEnd ℂ) (M.1 i j v) := by
      intro i j v
      have h : star M.1 = M.1 := M.2
      conv_lhs => rw [← h]
      rfl
    have h1 : trF M.1 M.1 = ∑ p : InfinitePlace E × Fin a × Fin a, ‖M.1 p.2.1 p.2.2 p.1‖ ^ 2 := by
      rw [trF_eq, Complex.re_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hM p.2.1 p.2.2, re_mul_conj]
    have h2 : ∑ p : InfinitePlace E × Fin a × Fin a, ‖(vecMulVec w (star w)) p.2.2 p.2.1 p.1‖ ^ 2 ≤ qf w ^ 2 := by
      rw [qf_eq, sq (∑ v : InfinitePlace E, ∑ i, ‖w i v‖ ^ 2)]
      refine le_trans (le_of_eq ?_) (sum_mul_le _ _ (fun v => by positivity) (fun v => by positivity))
      simp only [Fintype.sum_prod_type, Finset.sum_mul_sum, vecMulVec_apply, Pi.mul_apply, Pi.star_apply,
        norm_mul, norm_star, mul_pow, mul_comm]
    rw [h1, trF_eq]
    refine le_trans ?_ ((cs_norm _ _).trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
    exact sq_le_sq' (abs_le.1 (Complex.abs_re_le_norm _)).1 (abs_le.1 (Complex.abs_re_le_norm _)).2
  · rw [quad_eq]
    have hs : 0 ≤ ∑ v : InfinitePlace E, ‖(x ⬝ᵥ w) v‖ ^ 2 := by positivity
    rw [← Real.le_sqrt (norm_nonneg _) hs]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.le_sqrt (norm_nonneg _) hs]
    exact Finset.single_le_sum (f := fun v => ‖(x ⬝ᵥ w) v‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ v)
  · rw [quad_eq, qf_eq, qf_eq, mul_comm]
    refine le_trans ?_ (sum_mul_le _ _ (fun v => by positivity) (fun v => by positivity))
    refine Finset.sum_le_sum fun v _ => ?_
    have := cs_norm (fun i => x i v) (fun i => w i v)
    simpa [dotProduct, Finset.sum_apply] using this
  · rw [quad_eq, h]; simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.UnitaryGroupLieAlgebraEqSkewHermitian
section
open UpperTheory.V.Lit.Geo NumberField Matrix GlobalTheory.CuspRep Topology Filter

theorem UpperTheory.unitaryGroup_lieAlgebra_eq_skewHermitian :
    LatEx := by
  intro E _ _ a U hU
  let O : Set (Af E) := GroundTheory.Global.integralFiniteAdeles (𝓞 E) E
  have hOo : IsOpen O := GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 E) (K := E)
  have hOc : IsCompact O := GroundTheory.Global.isCompact_integralFiniteAdeles E
  let B : Set (Fin a → Af E) := Set.univ.pi fun _ => O
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => hOo
  have hBc : IsCompact B := isCompact_univ_pi fun _ => hOc
  have hB0 : (0 : Fin a → Af E) ∈ B := fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).zero_mem
  let L : AddSubgroup (Fin a → Af E) :=
    { carrier := {x | ∀ u ∈ U, x ᵥ* u.val ∈ B}
      zero_mem' := fun u _ => by rw [Matrix.zero_vecMul]; exact hB0
      add_mem' := fun {x y} hx hy u hu => by
        rw [Matrix.add_vecMul]
        exact fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).add_mem (hx u hu i hi) (hy u hu i hi)
      neg_mem' := fun {x} hx u hu => by
        rw [Matrix.neg_vecMul]
        exact fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).neg_mem (hx u hu i hi) }
  have hc : Continuous fun p : (Fin a → Af E) × GL (Fin a) (Af E) => p.1 ᵥ* p.2.val :=
    continuous_fst.matrix_vecMul (Units.continuous_val.comp continuous_snd)
  have hn : (L : Set (Fin a → Af E)) ∈ 𝓝 0 := by
    refine hU.eventually_forall_of_forall_eventually (x₀ := (0 : Fin a → Af E))
      (P := fun x (u : GL (Fin a) (Af E)) => x ᵥ* u.val ∈ B) fun u _ => ?_
    refine hc.continuousAt.eventually_mem (hBo.mem_nhds ?_)
    simpa only [Matrix.zero_vecMul] using hB0
  have ho : IsOpen (L : Set (Fin a → Af E)) := L.isOpen_of_mem_nhds hn
  refine ⟨L, ⟨ho, hBc.of_isClosed_subset (L.isClosed_of_isOpen ho) fun x hx => ?_⟩, fun u hu x hx v hv => ?_⟩
  · simpa only [Units.val_one, Matrix.vecMul_one] using hx 1 U.one_mem
  · rw [Matrix.vecMul_vecMul]
    exact hx (u * v) (U.mul_mem hu hv)
end

