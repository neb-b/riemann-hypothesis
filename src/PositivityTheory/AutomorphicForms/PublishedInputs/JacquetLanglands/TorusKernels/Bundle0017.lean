module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Qminor

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicTermsSetupProof
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc Matrix

namespace UpperTheory.Esk.HyperbolicSetupLemmas

section Gen

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem stab_open (ρ : Representation ℂ G V) (x : V) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    (hx : ∀ g ∈ U, ρ g x = x) : IsOpen {g | ρ g x = x} := by
  rw [isOpen_iff_mem_nhds]
  intro g₀ hg₀
  have ho : IsOpen ((fun g => g₀⁻¹ * g) ⁻¹' U) := hU.preimage (by fun_prop)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using h1)) fun g hg => ?_
  have h2 : ρ (g₀⁻¹ * g) x = x := hx _ hg
  have hg₀' : ρ g₀ x = x := hg₀
  change ρ g x = x
  calc ρ g x = ρ g₀ (ρ (g₀⁻¹ * g) x) := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = x := by rw [h2, hg₀']

def smV (ρ : Representation ℂ G V) : Submodule ℂ V where
  carrier := {x | IsOpen {g | ρ g x = x}}
  add_mem' := fun {x y} hx hy => stab_open ρ _ _ (IsOpen.inter hx hy) ⟨by simp, by simp⟩
    fun g hg => by
      have h1 : ρ g x = x := hg.1
      have h2 : ρ g y = y := hg.2
      rw [map_add (f := _), h1, h2]
  zero_mem' := by
    change IsOpen {g | ρ g 0 = 0}
    simp only [map_zero, Set.setOf_true]
    exact isOpen_univ
  smul_mem' := fun a x hx => stab_open ρ _ _ hx (by simp) fun g hg => by
    have h1 : ρ g x = x := hg
    rw [map_smul, h1]

theorem smV_stable (ρ : Representation ℂ G V) (g : G) : smV ρ ≤ Submodule.comap (ρ g) (smV ρ) := by
  intro x hx
  change IsOpen {h | ρ h (ρ g x) = ρ g x}
  refine stab_open ρ _ ((fun h => g⁻¹ * h * g) ⁻¹' {h | ρ h x = x}) ((show IsOpen {h | ρ h x = x} from hx).preimage (by fun_prop))
    (by simp) fun h hh => ?_
  have e : ρ (g⁻¹ * h * g) x = x := hh
  calc ρ h (ρ g x) = ρ g (ρ (g⁻¹ * h * g) x) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]
    _ = ρ g x := by rw [e]

theorem smV_smooth (ρ : Representation ℂ G V) : GlobalTheory.PRep.IsSmooth (ρ.subrepresentation (smV ρ) (smV_stable ρ)) := by
  intro x
  have e : {g | ρ.subrepresentation (smV ρ) (smV_stable ρ) g x = x} = {g | ρ g x.1 = x.1} := by
    ext g; exact Subtype.ext_iff
  rw [e]
  exact x.2

end Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem fix_of (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2) (hφ : IsHolV k c ω φ) :
    φ ∈ Hi.fixd (TR.finRep F 2) (Kc c) := by
  let ρ := (TR.finRep F 2).subrepresentation (smV (TR.finRep F 2)) (smV_stable _)
  have hx : φ ∈ smV (TR.finRep F 2) := hφ.aut.level
  have h := fixGlob F _ ρ (smV_smooth _) c ⟨φ, hx⟩ fun w u hu => Subtype.ext (hφ.level w u hu)
  intro u hu
  exact congrArg Subtype.val (h u hu)

private def rot (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
  val := !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]
  inv := !![fun v => Real.cos (θ v), fun v => -Real.sin (θ v); fun v => Real.sin (θ v), fun v => Real.cos (θ v)]
  val_inv := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
  inv_val := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith

omit [NumberField F] [IsTotallyReal F] in
private theorem rot_add (θ θ' : TR.Rinf F) : rot (θ + θ') = rot θ * rot θ' := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

theorem sign_holV {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) (v : InfinitePlace F) :
    ((ω.locInf v (-1) : ℂˣ) : ℂ) = Complex.exp (Complex.I * (k v : ℕ) * Real.pi) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (Subtype.ext (funext h))
  set e : TR.Rinf F := Pi.single v 1 with he
  have hr0 : rot ((0 : ℝ) • e) = 1 := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [rot]
  have hd0 : ∀ g, HasDerivAt (fun t : ℝ => φ.1 (g * TR.infGL F 2 (rot (t • e)))) (Complex.I * (k v : ℕ) * φ.1 g) 0 := fun g => by
    have h1 := TR.hasDerivAt_curve φ g (fun t : ℝ => rot (t • e))
      (TR.toL (Matrix.single 0 1 e) - TR.toL (Matrix.single 1 0 e)) hr0 (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
        have hc := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).cos
        have hs := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).sin
        fin_cases i <;> fin_cases j
        · simpa [rot] using hc
        · simpa [rot] using hs
        · simpa [rot] using hs.fun_neg
        · simpa [rot] using hc)
    rw [← TR.lie_apply, map_sub] at h1
    exact h1.congr_deriv (congrArg (fun x : TR.Sm F 2 => x.1 g) (hφ.wt v))
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rot (t • e))) with hf
  have hd : ∀ t, HasDerivAt f (Complex.I * (k v : ℕ) * f t) t := fun t => by
    have h1 := HasDerivAt.comp_sub_const t t ((sub_self t).symm ▸ hd0 (g * TR.infGL F 2 (rot (t • e))))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [mul_assoc, ← map_mul, ← rot_add, ← add_smul, add_sub_cancel]
  have hc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t * Complex.exp (-(Complex.I * (k v : ℕ) * t))) 0 t := fun t => by
    have h1 := (hd t).mul (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * (k v : ℕ))).fun_neg.cexp)
    exact h1.congr_deriv (by simp; ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hc t).differentiableAt) (fun t => (hc t).deriv) Real.pi 0
  have hu : (1 - 2 * e) * (1 - 2 * e) = 1 := by
    funext w
    by_cases h : w = v
    · subst h; simp [he]; norm_num
    · simp [he, h]
  let u : (TR.Rinf F)ˣ := ⟨1 - 2 * e, 1 - 2 * e, hu, hu⟩
  have h3 : rot (Real.pi • e) = GeneralLinearGroup.scalar (Fin 2) u := by
    ext i j w
    by_cases h : w = v
    · subst h
      fin_cases i <;> fin_cases j <;> simp [rot, u, he] <;> norm_num
    · fin_cases i <;> fin_cases j <;> simp [rot, u, he, h]
  have h4 : Units.map (GlobalTheory.CuspRep.corner (TR.sInf F)) u = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1) := by
    refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
    · change (1 - TR.infEq F 1 + TR.infEq F (1 - 2 * e)) w = Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w
      rw [map_one, sub_self, zero_add]
      change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((1 - 2 * e) w) = _
      by_cases h : w = v
      · subst h
        rw [show (1 - 2 * e) w = -1 by simp [he]; norm_num]
        simp
      · simp [he, h]
    · change (1 : Af F) - 0 + 0 = 1
      simp
  simp only [hf, hr0, h3, TR.infGL, map_one, mul_one] at h2
  rw [GlobalTheory.CuspRep.cornerGL_scalar, h4, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent] at h2
  rw [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, Complex.exp_neg, mul_right_comm,
    mul_eq_right₀ hg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at h2
  exact h2

theorem sgn_of {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) : Sgn k ω := by
  intro v
  rw [sign_holV hφ h0 v, show Complex.I * ((k v : ℕ) : ℂ) * (Real.pi : ℂ) = (k v : ℕ) * ((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I]

theorem fin_zc (z : (Af F)ˣ) : finGL F 2 (zc F z) = GeneralLinearGroup.scalar (Fin 2) (finId F z) := by
  rw [zc, finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  rfl

theorem chi_of {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) : ∃ χ, IsChi c ω χ := by
  have hfix := fix_of k c ω φ hφ
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (Subtype.ext (funext h))
  have h1 : ∀ z, zc F z ∈ Kc c → (ω.1.comp (finId F)) z = 1 := by
    intro z hz
    have e := congrArg (fun ψ : TR.Sm F 2 => ψ.1 g) (hfix _ hz)
    change φ.1 (g * finGL F 2 (zc F z)) = φ.1 g at e
    rw [fin_zc, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent, mul_eq_right₀ hg] at e
    exact Units.ext e
  obtain ⟨χ, hχ⟩ := exChi (GF F) (Af F)ˣ (Kc c) (zc F) (ω.1.comp (finId F)) (fun z => zc_center z) h1
  exact ⟨χ, hχ⟩

end UpperTheory.Esk.HyperbolicSetupLemmas

open UpperTheory.Esk.HyperbolicSetupLemmas in
theorem UpperTheory.Esk.hyperbolic_terms_setup_proof : UpperTheory.Esk.H0 := by
  intro F _ _ _ k c ω φ hφ h0
  exact ⟨sgn_of hφ h0, fix_of k c ω φ hφ, chi_of hφ h0⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfGMod
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped NNReal

namespace UpperTheory.Esk.ModulusCharacterLemmas

variable {F : Type} [Field F] [NumberField F]

theorem tnn {e : ℝ≥0} (he : e ≠ 0) (m : ℤ) : WithZeroMulInt.toNNReal he (WithZero.exp m) = e ^ m := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]; rfl

theorem exp_mul_pow (m : ℤ) :
    WithZero.exp m * (WithZero.exp (-1 : ℤ)) ^ m = (1 : WithZero (Multiplicative ℤ)) := by
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_zpow, ← WithZero.coe_mul,
    ← ofAdd_zsmul, ← ofAdd_add]
  simp

theorem val_exp {w : Pl F} {x : w.adicCompletion F} (hx : x ≠ 0) : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
  ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm⟩

theorem norm_eq (w : Pl F) {x : w.adicCompletion F} {m : ℤ} (hm : Valued.v x = WithZero.exp m) :
    ‖x‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ m := by
  rw [FinitePlace.norm_def (x := x), hm, tnn, NNReal.coe_zpow, NNReal.coe_natCast]

theorem normV_eq (w : Pl F) : normV w = Ideal.absNorm w.asIdeal := by
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem nu_nat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (h : ¬ l ∣ n) : nu ι (n : ℂ) = 1 := by
  have e : ι.symm (n : ℂ) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l]) := by rw [map_natCast, map_natCast]
  apply NNReal.coe_injective
  rw [nu_apply, coe_nnnorm, e, norm_algebraMap',
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h), NNReal.coe_one]

theorem not_dvd (w : Pl F) {l : ℕ} [hl : Fact l.Prime] (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  intro hd
  haveI := w.isPrime
  have hne : normV w ≠ 0 := by
    rw [normV_eq]; have := HeightOneSpectrum.one_lt_absNorm w; omega
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  have hd' : l ∣ Fintype.card (𝓞 F ⧸ w.asIdeal) := by rw [Fintype.card_eq_nat_card]; exact hd
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card l hd'
  have h1 : (l : 𝓞 F ⧸ w.asIdeal) * a = 0 := by rw [← nsmul_eq_mul, ← ha, addOrderOf_nsmul_eq_zero]
  have h2 : (l : 𝓞 F ⧸ w.asIdeal) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ne, Ideal.Quotient.eq_zero_iff_mem]; exact h
  have h3 : a = 0 := (mul_eq_zero.1 h1).resolve_left h2
  rw [h3, addOrderOf_zero] at ha
  exact hl.out.one_lt.ne ha

theorem away {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Pl F) (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {x : w.adicCompletion F} (hx : x ≠ 0) : nu ι (‖x‖ : ℂ) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  rw [norm_eq w hm, Complex.ofReal_zpow, Complex.ofReal_natCast, map_zpow₀, ← normV_eq, nu_nat ι (not_dvd w h),
    one_zpow]

theorem atL {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (v : InfinitePlace F)
    {x : (D.pl v).adicCompletion F} (hx : x ≠ 0) : nu ι ((‖x‖ : ℂ) * D.em v x) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL
  have hLv : Valued.v L = WithZero.exp (-1 : ℤ) := D.unif v
  have hL0 : L ≠ 0 := fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm
  have hemL : D.em v L = (l : ℂ) := map_natCast _ l
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hy : Valued.v (x * L ^ m) = 1 := by rw [map_mul, map_zpow₀, hLv, hm, exp_mul_pow]
  have hnu : nu ι (D.em v (x * L ^ m)) = 1 :=
    le_antisymm ((D.le v _).2 hy.le) (not_lt.1 fun h => ((D.lt v _).1 h).ne hy)
  have hn : ‖x‖ = (l : ℝ) ^ m := by rw [norm_eq _ hm, ← normV_eq, D.norm v]
  have e : (‖x‖ : ℂ) * D.em v x = D.em v (x * L ^ m) := by
    rw [hn, map_mul, map_zpow₀, hemL, Complex.ofReal_zpow, Complex.ofReal_natCast]
    ring
  rw [e, hnu]

theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem fin_supp (y : (Af F)ˣ) : (Function.mulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖).Finite := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

end UpperTheory.Esk.ModulusCharacterLemmas

open UpperTheory.Esk.ModulusCharacterLemmas in
theorem UpperTheory.Esk.pf_GMod : UpperTheory.Esk.GMod := by
  intro F _ _ l _ ι D z
  have hz : ∀ w, pLoc F w (z : Af F) ≠ 0 := fun w => (z.isUnit.map (pLoc F w)).ne_zero
  have habs : absF z = ∏ᶠ w : Pl F, ‖pLoc F w (z : Af F)‖ := rfl
  refine ⟨?_, ?_⟩
  · rw [habs]
    exact finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w => norm_pos_iff.2 (hz w)
  classical
  have hfin := fin_supp z
  set s : Finset (Pl F) := hfin.toFinset ∪ Finset.univ.image D.pl with hs_def
  have hs : absF z = ∏ w ∈ s, ‖pLoc F w (z : Af F)‖ := by
    rw [habs]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    rw [hs_def, Finset.coe_union]
    exact Or.inl (hfin.mem_toFinset.2 hw)
  have hprod : ∏ v, D.ea v (z : Af F) = ∏ w ∈ s, ∏ v ∈ Finset.univ.filter (fun v => D.pl v = w), D.ea v (z : Af F) :=
    (Finset.prod_fiberwise_of_maps_to (fun v _ => by simp [hs_def]) _).symm
  rw [hs, hprod, Complex.ofReal_prod, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  by_cases hw : ∃ v, D.pl v = w
  · obtain ⟨v, rfl⟩ := hw
    have e : Finset.univ.filter (fun u => D.pl u = D.pl v) = {v} := by
      ext u; simp [D.inj.eq_iff]
    rw [e, Finset.prod_singleton]
    exact atL D v (hz _)
  · have e : Finset.univ.filter (fun u => D.pl u = w) = ∅ := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hw ⟨u, h⟩
    rw [e, Finset.prod_empty, mul_one]
    exact away ι w (fun h => hw (D.surj w h)) (hz w)
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHCap
section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

namespace UpperTheory.Esk.CasimirEigenvalueLemmas

theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {k c} {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : UpperTheory.Esk.IsHolV k c ω φ) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ.cent, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u

end UpperTheory.Esk.CasimirEigenvalueLemmas

open UpperTheory.Esk.CasimirEigenvalueLemmas in
theorem UpperTheory.Esk.pf_HCap : UpperTheory.Esk.HCap := by
  intro F _ _ _ k c ω hω φ hφ
  refine ⟨by simpa using lie_scalar hω hφ 1, fun v u => ?_⟩
  have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
    classical
    rw [← lie_scalar hω hφ (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have := casimir _ (TR.glRel_Eop v) (k v) φ h0 (hφ.wt v) (hφ.low v) u
  rw [← this, TR.cap]
  norm_num
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHFin
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.FiniteLevelGroupLemmas

def Gm (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    (X (InfinitePlace F) × GF F → ℂ) →ₗ[ℂ] (GA F 2 → ℂ) where
  toFun f := Classical.choose ((h F k).1 f)
  map_add' f f' := by
    have e := (h F k).2.2.2.1 f f' _ _ 1 (Classical.choose_spec ((h F k).1 f)) (Classical.choose_spec ((h F k).1 f'))
    simp only [one_smul] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (f + f'))) e
  map_smul' s f := by
    have e := (h F k).2.2.2.1 0 f 0 _ s (h F k).2.2.2.2.1 (Classical.choose_spec ((h F k).1 f))
    simp only [zero_add] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (s • f))) e

theorem rel (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ)
    (f : X (InfinitePlace F) × GF F → ℂ) : Rel k f (Gm h F k f) :=
  Classical.choose_spec ((h F k).1 f)

theorem inj (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    Function.Injective (Gm h F k) := by
  intro f f' e
  have h2 := rel h F k f'
  rw [← e] at h2
  exact (h F k).2.2.1 f f' _ (rel h F k f) h2

end UpperTheory.Esk.FiniteLevelGroupLemmas

theorem UpperTheory.Esk.pf_HFin : UpperTheory.Esk.HRel → UpperTheory.Esk.H2a → UpperTheory.Esk.H2d → UpperTheory.Esk.H2e → UpperTheory.Esk.HFinC → UpperTheory.Esk.HFin := by
  intro hR h2a h2d h2e hC F _ _ _ k c hc ω χ hω hχ hS hk
  classical
  let S : Set (TR.Sm F 2) := {φ | IsHolV k c ω φ ∧ TR.IsCuspForm φ}
  have : FiniteDimensional ℂ (Submodule.span ℂ S) := hC F k c hc ω hω
  let W : Submodule ℂ (GA F 2 → ℂ) := (Submodule.span ℂ S).map (TR.Sm F 2).subtype
  have : FiniteDimensional ℂ W := inferInstance
  let p := Submodule.span ℂ {f | (mkDat c χ).IsForm k f}
  have hle : p.map (FiniteLevelGroupLemmas.Gm hR F k) ≤ W := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hrel := FiniteLevelGroupLemmas.rel hR F k f
    obtain ⟨hs, hhol⟩ := h2d F k c hc ω χ hω hχ hS hk f _ hf hrel
    have hb := (h2a F k c hc ω χ hω hχ hS hk f _ hf hrel).2.2.2
    have hcusp := h2e F k c ω ⟨_, hs⟩ hω hk hhol hb
    exact ⟨⟨_, hs⟩, Submodule.subset_span ⟨hhol, hcusp⟩, rfl⟩
  have : FiniteDimensional ℂ (p.map (FiniteLevelGroupLemmas.Gm hR F k)) := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (FiniteLevelGroupLemmas.inj hR F k) p).symm
end
end

