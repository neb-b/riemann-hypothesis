module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHFinC
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors UpperTheory.V.Sd
open Neutral.B1 Formalism.L2.Host UpperTheory.V.Base

namespace UpperTheory.Esk.HFinCAux

theorem exists_rep {K ι A : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [Finite ι] (e : ι → K) (r : A → K)
    (χ : A → ℂ) (h : ∀ x, ∃ i a, x = e i * r a) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧
        ∀ f : K → ℂ, Continuous f → (∀ x a, f (x * r a) = χ a * f x) → f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  let V : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ x a, f (x * r a) = χ a * f x}
      add_mem' := fun hf hg => ⟨hf.1.add hg.1, fun x a => by simp [hf.2, hg.2, mul_add]⟩
      zero_mem' := ⟨continuous_const, fun x a => by simp⟩
      smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun x a => by simp [hf.2, mul_left_comm]⟩ }
  haveI : FiniteDimensional ℂ V := by
    refine Module.Finite.of_injective ((LinearMap.funLeft ℂ ℂ e).comp V.subtype) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    ext x
    obtain ⟨i, a, rfl⟩ := h x
    have : f.1 (e i) = 0 := congrFun hf i
    rw [f.2.2, this]; simp
  let L : Representation ℂ K V :=
    { toFun := fun k =>
        { toFun := fun f => ⟨fun x => f.1 (k⁻¹ * x), f.2.1.comp (continuous_const.mul continuous_id), fun x a => by
            simp only [← mul_assoc, f.2.2]⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp
      map_mul' := fun k k' => by ext f x; simp [mul_assoc] }
  refine ⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, L.dual, fun l w => ?_, fun f hf hf' => ?_⟩
  · obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ V).surjective l
    change Continuous fun k => w (L k⁻¹ f)
    refine w.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun x => ?_) _)
    exact f.2.1.comp (continuous_inv.inv.mul continuous_const)
  · refine Submodule.subset_span ⟨Module.Dual.eval ℂ V ⟨f, hf, hf'⟩, (LinearMap.proj 1).comp V.subtype, funext fun k => ?_⟩
    change f k = f (k⁻¹⁻¹ * 1)
    simp

variable {F : Type} [Field F] [NumberField F]

theorem local_mem_principal_congruence {M : ℕ} (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (hM : (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    {k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 M) : GeneralLinearGroup.map (pLoc F w) k ∈ K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat F →+* w.adicCompletionIntegers F :=
    ((pLoc F w).comp (Ohat F).subtype).codRestrict (w.adicCompletionIntegers F) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  have key : GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)) (GeneralLinearGroup.map p g) = 1 := by
    let q := Ideal.quotientMap (I := Ideal.span {(M : ↥(Ohat F))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
    have := congrArg (GeneralLinearGroup.map q) (MonoidHom.mem_ker.1 hg)
    rw [map_one] at this
    rw [← this]
    rfl
  exact Subgroup.mem_comap.2 (key ▸ one_mem _)

theorem exists_level (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c w := by
  refine ⟨∏ w ∈ hc.toFinset, Ideal.absNorm w.asIdeal ^ c w, ?_, fun w => ?_⟩
  · refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_)
    exact fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · by_cases h : c w = 0
    · simp [h]
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 F) => Ideal.absNorm w.asIdeal ^ c w)
      (hc.mem_toFinset.2 h)
    rw [hm, Nat.cast_mul, Nat.cast_pow]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    have h1 := Ideal.absNorm_mem w.asIdeal
    rw [← map_natCast (algebraMap (𝓞 F) (w.adicCompletionIntegers F))]
    generalize (Ideal.absNorm w.asIdeal : 𝓞 F) = x at h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt ((w.valuation_lt_one_iff_mem x).2 h1)
    exact h2

theorem fixed_KLev {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) {M : ℕ} (v : V)
    (ho : IsOpen {k | ρ k v = v}) (h : ∀ w, ∀ k ∈ KLev F 2 M, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) :
    ∀ k ∈ KLev F 2 M, ρ k v = v := by
  classical
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ k ∈ KAway 2 M S, ρ k v = v) → ∀ k ∈ KAway 2 M ∅, ρ k v = v := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      refine fun hv => ih fun k hk => ?_
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 := h w k (mem_KAway.1 hk).1
      have h4 := hv _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) (ho.mem_nhds (by simp))
  exact fun k hk => key S (fun k hk => hS hk) k (mem_KAway.2 ⟨hk, by simp⟩)

noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

omit [NumberField F] in
theorem rot_add (θ η : TR.Rinf F) : rot (θ + η) = rot θ * rot η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
theorem rot_zero : rot (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

theorem cont (φ : TR.Sm F 2) (g : GA F 2) : Continuous fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g := by
  have e : (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) = fun k : TR.Kinf F 2 => TR.chart φ.1 g (TR.toL k.1) :=
    funext fun k => (TR.chart_val φ.1 g (Unitary.toUnits k)).symm
  rw [e]
  exact (φ.2 g).continuousOn.comp_continuous continuous_subtype_val fun k => TR.val_mem_invSet (Unitary.toUnits k)

theorem rot_eig (φ : TR.Sm F 2) (z : InfinitePlace F → ℂ) (h : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z v • φ) (g : GA F 2) (θ : TR.Rinf F) :
    φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot θ))) = Complex.exp (∑ v, z v * (θ v : ℂ)) * φ.1 g := by
  classical
  set μ : ℂ := ∑ v, z v * (θ v : ℂ) with hμ
  let X : TR.Lie F 2 := TR.toL !![0, θ; -θ, 0]
  have hX : X = ∑ v, θ v • (TR.toL (Matrix.single 0 1 (Pi.single v 1)) - TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [X, Finset.sum_apply, Pi.single_apply]
  have hL : TR.lie F 2 X φ = μ • φ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hX, map_sum, LinearMap.sum_apply, hμ, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, Complex.coe_smul, ← h v]
    simp only [TR.Eop]
  have hc : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (t • θ))).val) X 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    have h1 : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
    fin_cases i <;> fin_cases j
    · simpa [X, rot] using h1.cos
    · simpa [X, rot] using h1.sin
    · simpa [X, rot] using h1.sin.fun_neg
    · simpa [X, rot] using h1.cos
  let f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ))))
  have hf : ∀ t, HasDerivAt f (μ * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ)))) (fun s => Unitary.toUnits (rot (s • θ))) X
      (by rw [zero_smul, rot_zero, map_one]) hc
    rw [← TR.lie_apply, hL] at h1
    have h2 : HasDerivAt (fun s => f (t + s)) (μ * f t) 0 := by
      simpa only [f, add_smul, rot_add, map_mul, mul_assoc] using! h1
    have h3 := HasDerivAt.comp_sub_const t t (f := fun s => f (t + s)) (by rw [sub_self]; exact h2)
    simpa using h3
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-μ * s) * f s) 0 t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => -μ * (s : ℂ)) (-μ) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-μ)
    exact (h1.cexp.fun_mul (hf t)).congr_deriv (by ring)
  have h4 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, one_smul, zero_smul, rot_zero, map_one, mul_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul] at h4
  rw [← h4, ← mul_assoc, ← Complex.exp_add]
  simp

end UpperTheory.Esk.HFinCAux

open UpperTheory.Esk.HFinCAux in
theorem UpperTheory.Esk.pf_HFinC : UpperTheory.Esk.HCap → UpperTheory.Esk.HFinC := by
  intro hcap F _ _ _ k c hc ω hω
  obtain ⟨M, hM1, hM⟩ := exists_level c hc
  have hfix : ∀ φ : TR.Sm F 2, UpperTheory.Esk.IsHolV k c ω φ → ∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ := fun φ hφ =>
    fixed_KLev _ φ hφ.aut.level fun w u hu => hφ.level w _ (local_mem_principal_congruence w _ (hM w) hu)
  obtain ⟨W, _, _, _, ρ, hρ, hf⟩ := exists_rep (eps (F := F)) (rot (F := F))
    (fun θ => Complex.exp (∑ v, Complex.I * (k v : ℂ) * (θ v : ℂ))) dec
  have := UpperTheory.V.Af.cuspFormsFiniteReal F 2 (KLev F 2 M) (isOpen_KLev hM1) W ρ hρ
    fun v u => (u + ((k v : ℂ) - 1) / 2) * (u - ((k v : ℂ) - 1) / 2)
  refine Submodule.finiteDimensional_of_le (S₂ := _) (Submodule.span_mono (fun φ hφ => ?_) : _ ≤ Submodule.span ℂ
    {φ : TR.Sm F 2 | TR.IsCuspForm φ ∧ (∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ) ∧
      (∀ g : GA F 2, (fun u : TR.Kinf F 2 => (TR.cptRep F 2 u φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
      ∀ v u, TR.cap v u φ = ((u + ((k v : ℂ) - 1) / 2) * (u - ((k v : ℂ) - 1) / 2)) • φ})
  obtain ⟨hφ', hcusp⟩ := hφ
  refine ⟨hcusp, hfix φ hφ', fun g => hf _ (cont φ g) fun x θ => ?_, (hcap F k c ω hω φ hφ').2⟩
  have := rot_eig φ (fun v => Complex.I * (k v : ℂ)) hφ'.wt (g * TR.infGL F 2 (Unitary.toUnits x)) θ
  rw [mul_assoc, ← map_mul, ← map_mul] at this
  exact this
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHRel
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.HeckeRelationLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def asm (g : InfinitePlace F → GL (Fin 2) ℝ) : GL (Fin 2) (TR.Rinf F) where
  val := Matrix.of fun i j v => (g v).val i j
  inv := Matrix.of fun i j v => (g v)⁻¹.val i j
  val_inv := by
    refine Matrix.ext fun i j => funext fun v => ?_
    have h := congrFun (congrFun (g v).mul_inv i) j
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (g v).val i 0 * (g v)⁻¹.val 0 j + (g v).val i 1 * (g v)⁻¹.val 1 j = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v
    rw [h]
    fin_cases i <;> fin_cases j <;> rfl
  inv_val := by
    refine Matrix.ext fun i j => funext fun v => ?_
    have h := congrFun (congrFun (g v).inv_mul i) j
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (g v)⁻¹.val i 0 * (g v).val 0 j + (g v)⁻¹.val i 1 * (g v).val 1 j = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v
    rw [h]
    fin_cases i <;> fin_cases j <;> rfl

omit [NumberField F] [IsTotallyReal F] in
theorem gv_asm (g : InfinitePlace F → GL (Fin 2) ℝ) (v : InfinitePlace F) : gv v (asm g) = g v :=
  Units.ext (Matrix.ext fun _ _ => rfl)

omit [NumberField F] [IsTotallyReal F] in
theorem exists_g (hc : B1c) (z : X (InfinitePlace F)) : ∃ g : GL (Fin 2) (TR.Rinf F), (fun v => gv v g • iP) = z := by
  choose h _ _ hh using fun v => hc.2.2.2.2.2 (z v)
  exact ⟨asm h, funext fun v => by rw [gv_asm, hh]⟩

theorem inf_of (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    Matrix.GeneralLinearGroup.map (TR.pInf F) (TR.infGL F 2 g * finGL F 2 x) = g := by
  rw [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one]

theorem fin_of (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    Matrix.GeneralLinearGroup.map (pFin F) (TR.infGL F 2 g * finGL F 2 x) = x := by
  rw [map_mul, TR.pFin_infGL, pFin_finGL, one_mul]

end UpperTheory.Esk.HeckeRelationLemmas

open UpperTheory.Esk in
theorem UpperTheory.Esk.pf_HRel : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.HRel := by
  intro hb hc F _ _ _ k
  have hne : ∀ g : GL (Fin 2) (TR.Rinf F), ∏ v, j1 (k v) (gv v g) iP ≠ 0 :=
    fun g => Finset.prod_ne_zero_iff.2 fun v _ => hb.2.1 _ _ _
  refine ⟨fun f => ⟨fun a => f (fun v => gv v (Matrix.GeneralLinearGroup.map (TR.pInf F) a) • iP,
      Matrix.GeneralLinearGroup.map (pFin F) a) / ∏ v, j1 (k v) (gv v (Matrix.GeneralLinearGroup.map (TR.pInf F) a)) iP,
      fun g x => ?_⟩, fun f φ φ' h h' => ?_, fun f f' φ h h' => ?_, fun f f' φ φ' s h h' => ?_, fun g x => ?_,
      fun n a f φ h => ?_⟩
  · simp only [HeckeRelationLemmas.inf_of, HeckeRelationLemmas.fin_of]
    exact div_mul_cancel₀ _ (hne g)
  · funext a
    rw [← TR.infGL_mul_finGL a]
    exact mul_right_cancel₀ (hne _) ((h _ _).trans (h' _ _).symm)
  · funext p
    obtain ⟨z, x⟩ := p
    obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    rw [← h g x, ← h' g x]
  · intro g x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, h g x, h' g x]
  · simp
  · intro g x
    simp only [Dat.Op, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change φ.1 (TR.infGL F 2 g * finGL F 2 x * finGL F 2 (a i)) * _ = _
    rw [mul_assoc, ← map_mul, h g (x * a i)]
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfTrCong
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.TraceCongruenceBounds

open UpperTheory.Esk

theorem nu_two {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (ι : Qbar l ≃+* ℂ) : nu ι 2 = 1 := by
  have hle : ∀ m : ℕ, nu ι (m : ℂ) ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ]; exact (nu ι).map_add_le ih (by simp)
  have hlt : nu ι (l : ℂ) < 1 := by
    rw [nu_apply, map_natCast, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l]
    exact lt_of_eq_of_lt (PadicAlgCl.norm_extends l _) Padic.norm_p_lt_one
  obtain ⟨m, hm⟩ := (Fact.out : l.Prime).odd_of_ne_two hl
  refine le_antisymm (by simpa using hle 2) (not_lt.1 fun h2 => ?_)
  have e : (1 : ℂ) = (l : ℂ) - 2 * (m : ℂ) := by rw [hm]; push_cast; ring
  have : nu ι ((l : ℂ) - 2 * (m : ℂ)) < 1 := by
    refine (nu ι).map_sub_lt hlt ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hle m)) h2
  rw [← e, map_one] at this
  exact lt_irrefl _ this

theorem sum_bound (ν : Valuation ℂ ℝ≥0) {β : Type*} (s : Finset β) (u x y : β → ℂ) (m : ℝ≥0)
    (hu : ∀ j ∈ s, ν (u j) ≤ 1)
    (h : ∀ j ∈ s, u j ≠ 0 → ν (x j) ≤ 1 ∧ ν (y j) ≤ 1 ∧ ν (x j - y j) ≤ m) :
    ν (∑ j ∈ s, u j * x j) ≤ 1 ∧ ν (∑ j ∈ s, u j * y j) ≤ 1 ∧
      ν (∑ j ∈ s, u j * x j - ∑ j ∈ s, u j * y j) ≤ m := by
  have key : ∀ j ∈ s, ∀ (z : ℂ) (b : ℝ≥0), (u j ≠ 0 → ν z ≤ b) → ν (u j * z) ≤ b := by
    intro j hj z b hz
    by_cases h0 : u j = 0
    · simp [h0]
    · rw [map_mul]
      exact le_trans (mul_le_mul' (hu j hj) (hz h0)) (by simp)
  refine ⟨ν.map_sum_le fun j hj => key j hj _ _ fun h0 => (h j hj h0).1,
    ν.map_sum_le fun j hj => key j hj _ _ fun h0 => (h j hj h0).2.1, ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine ν.map_sum_le fun j hj => ?_
  rw [← mul_sub]
  exact key j hj _ _ fun h0 => (h j hj h0).2.2

theorem geo_expand {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf) (k : I → ℕ) {n : ℕ}
    (a : Fin n → Gf) (S : Finset (D.Cj × D.Om)) (z : ℂ) :
    z * geo D k a S = ∑ q ∈ S ×ˢ (Finset.univ : Finset (Fin n)),
      ((Nat.card (MulAction.stabilizer (PG F) q.1) : ℂ)⁻¹ *
        D.ee ((D.rep q.1.2)⁻¹ * (D.j (D.el q.1.1).out)⁻¹ * D.rep q.1.2 * a q.2)) *
      (z * D.orb k (D.el q.1.1).out) := by
  rw [Finset.sum_product, geo, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Dat.Te, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem ee_mem {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) {x : Gf} (h : D.ee x ≠ 0) : x ∈ D.H := by
  by_contra hx
  exact h (by simp [Dat.ee, hx])

theorem nu_ee {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)
    {m : ℕ} (hm0 : 0 < m) (hm : ∀ h, D.χ h ^ m = 1) (x : Gf) : nu ι (D.ee x) ≤ 1 := by
  unfold Dat.ee
  split_ifs with hx
  · have e : (nu ι (D.χ ⟨x, hx⟩ : ℂ)) ^ m = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hm, Units.val_one, map_one]
    exact (pow_le_one_iff hm0.ne').1 e.le
  · simp

theorem nu_card {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (ι : Qbar l ≃+* ℂ) {G : Type*} [Group G] (S : Subgroup G)
    (hS : ∃ n, Nat.card S = 2 ^ n) : nu ι ((Nat.card S : ℂ)⁻¹) = 1 := by
  obtain ⟨n, hn⟩ := hS
  rw [map_inv₀, hn, Nat.cast_pow, map_pow, Nat.cast_ofNat, nu_two hl, one_pow, inv_one]

theorem stab_le {G A B : Type*} [Group G] [MulAction G A] [MulAction G B] (p : A × B) :
    MulAction.stabilizer G p ≤ MulAction.stabilizer G p.2 := fun g hg => by
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  exact congrArg Prod.snd hg

theorem geo_bound (ν : Valuation ℂ ℝ≥0) {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)
    (k k' : I → ℕ) {n : ℕ} (a : Fin n → Gf) (S : Finset (D.Cj × D.Om)) (z z' : ℂ) (m : ℝ≥0)
    (hu : ∀ p ∈ S, ∀ i, ν ((Nat.card (MulAction.stabilizer (PG F) p) : ℂ)⁻¹ *
        D.ee ((D.rep p.2)⁻¹ * (D.j (D.el p.1).out)⁻¹ * D.rep p.2 * a i)) ≤ 1)
    (h : ∀ p ∈ S, ∀ i, D.ee ((D.rep p.2)⁻¹ * (D.j (D.el p.1).out)⁻¹ * D.rep p.2 * a i) ≠ 0 →
      ν (z * D.orb k (D.el p.1).out) ≤ 1 ∧ ν (z' * D.orb k' (D.el p.1).out) ≤ 1 ∧
        ν (z * D.orb k (D.el p.1).out - z' * D.orb k' (D.el p.1).out) ≤ m) :
    ν (z * geo D k a S) ≤ 1 ∧ ν (z' * geo D k' a S) ≤ 1 ∧ ν (z * geo D k a S - z' * geo D k' a S) ≤ m := by
  rw [geo_expand, geo_expand]
  refine sum_bound ν _ _ _ _ m (fun q hq => hu q.1 (Finset.mem_product.1 hq).1 q.2) fun q hq hne => ?_
  exact h q.1 (Finset.mem_product.1 hq).1 q.2 (right_ne_zero_of_mul hne)

end UpperTheory.Esk.TraceCongruenceBounds

open UpperTheory.Esk UpperTheory.Esk.TraceCongruenceBounds in
theorem UpperTheory.Esk.pf_TrCong : UpperTheory.Esk.TF → UpperTheory.Esk.DAx → UpperTheory.Esk.DTwo → UpperTheory.Esk.DGood → UpperTheory.Esk.GTerm → UpperTheory.Esk.H0b → UpperTheory.Esk.HFin → UpperTheory.Esk.TrCong := by
  intro hTF hDAx hTwo hGood hGT hH0b hFin
  intro F _ _ _ hd l _ hl ι L k₀ hk₀ c hc hcL hu ω χ hω hχ hS N t ht W r hr hW n a hreps h h'
  obtain ⟨⟨m, hm0, hm⟩, hsg⟩ := hH0b F (fun _ => k₀) c ω χ hω hχ
  have hS' : Sgn (fun v => k₀ + 2 * t v) ω := fun v => by
    rw [hS v, pow_add, pow_mul]; simp
  have hax : (mkDat c χ).Ax := hDAx F hd c hc χ ⟨m, hm0, hm⟩
  obtain ⟨hgood, hreg⟩ := hGood F c ω χ hχ W n a hreps
  have hreg' : (mkDat c χ).Reg a := by
    apply hreg
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    classical
    exact ⟨L.pl v, List.count_pos_iff.1 (le_trans hr (hW v)), by rw [hcL v]; exact one_ne_zero⟩
  obtain ⟨S, hFam, hT⟩ := hTF F (InfinitePlace F) (GF F) (mkDat c χ) hax (Fin n) a
  have hyp0 : (mkDat c χ).Hyp (fun _ => k₀) a := ⟨hax, fun _ => hk₀, (hsg hS).1, hgood, hreg'⟩
  have hyp1 : (mkDat c χ).Hyp (fun v => k₀ + 2 * t v) a :=
    ⟨hax, fun _ => by omega, ((hH0b F _ c ω χ hω hχ).2 hS').1, hgood, hreg'⟩
  have fd0 : FiniteDimensional ℂ ((mkDat c χ).M fun _ => k₀) := hFin F _ c hc ω χ hω hχ hS fun _ => by omega
  have fd1 : FiniteDimensional ℂ ((mkDat c χ).M fun v => k₀ + 2 * t v) :=
    hFin F _ c hc ω χ hω hχ hS' fun _ => by omega
  rw [hT _ hyp0 fd0 h, hT _ hyp1 fd1 h']
  refine geo_bound (nu ι) (mkDat c χ) _ _ a S _ _ _ ?_ ?_
  · intro p hp i
    have hp' := hFam p hp
    rw [map_mul, nu_card hl ι _ (hTwo F c χ hu p.2 _ (stab_le p) hp'.2), one_mul]
    exact nu_ee ι _ hm0 hm _
  · intro p hp i hne
    exact hGT F l ι L c χ hcL k₀ (by omega) N t ht W r hr hW n a hreps _ _ i (hFam p hp).1 (ee_mem _ hne)
end
end

