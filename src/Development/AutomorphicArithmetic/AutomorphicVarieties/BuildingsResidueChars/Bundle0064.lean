module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ComplexConjugationsAreConjugate
section
theorem UpperTheory.complex_conjugations_are_conjugate :
    UpperTheory.V.Sd.S2.ConjCc := by
  intro Ω _ _ _ a b ha hb
  obtain ⟨j, hj⟩ := ha
  obtain ⟨j', hj'⟩ := hb
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j j'
    (Subsingleton.elim _ _)
  have h : ∀ x, j (σ.symm x) = j' x := fun x => by
    rw [← hσ]; rfl
  refine isConj_iff.2 ⟨σ, ?_⟩
  refine AlgEquiv.ext fun x => ?_
  apply j'.injective
  rw [hj', ← h, ← h]
  change j (σ.symm (σ (a (σ.symm x)))) = _
  rw [AlgEquiv.symm_apply_apply, hj]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermAutomorphy
section
open UpperTheory.V.Sd.Eis

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
private theorem ct_cont_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) :
    Continuous (TR.infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (TR.sInf F : TR.Rinf F → Ad F) := (TR.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
private theorem ct_aff_add (F : Type) [Field F] [NumberField F] (y : F) (x : Ad F) :
    (aff 1 (algebraMap F (Ad F) y + x) : GA F 2) = ratGL F 2 (aff 1 y) * aff 1 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aff, ratGL, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
private theorem ct_level (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a) (X : TR.Lie F a)
    (h : IsOpen {k | TR.finRep F a k φ = φ}) : IsOpen {k | TR.finRep F a k (TR.lie F a X φ) = TR.lie F a X φ} := by
  let S : TR.Sm F a → Subgroup (GL (Fin a) (Af F)) := fun ψ =>
    { carrier := {k | TR.finRep F a k ψ = ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  refine Subgroup.isOpen_mono (H₁ := S φ) (H₂ := S (TR.lie F a X φ)) (fun k hk => ?_) h
  have hk' : TR.rt F a (finGL F a k) φ = φ := hk
  have e := LinearMap.congr_fun (TR.lie_rt_fin X k) φ
  rw [Module.End.mul_apply, Module.End.mul_apply, hk'] at e
  exact e.symm

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.constant_term_automorphy :
    UpperTheory.V.Sd.Eis.SmCont → UpperTheory.V.Sd.Eis.PerMean → UpperTheory.V.Sd.Eis.PerDeriv → UpperTheory.V.Sd.Eis.BlockTop → UpperTheory.V.Sd.Eis.CtLie := by
  intro hS hM hD hB F _ _ _ _ _ μ _ D hF φ hl ho X
  have hl' : ∀ γ g, (TR.lie F 2 X φ).1 (ratGL F 2 γ * g) = (TR.lie F 2 X φ).1 g := by
    intro γ g
    have e : TR.chart φ.1 (ratGL F 2 γ * g) = TR.chart φ.1 g := by
      funext x
      simp only [TR.chart, mul_assoc, hl]
    simp only [TR.lie_apply, TR.lieD, e]
  have hc' : Continuous (TR.lie F 2 X φ).1 := hS F 2 _ (ct_level F 2 φ X ho)
  have hc : Continuous φ.1 := hS F 2 _ ho
  refine ⟨⟨hl', hc'⟩, fun c hcc hmul hder g => ?_⟩
  obtain ⟨i1, i2, i3, i4, hco, hu, hx⟩ := hB F
  have h0 : c 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hfin := (hM (NA F) (ratN F 2 1) hco μ D hF).1
  have hcont : Continuous fun p : NA F × ℝ => (unip p.1 : GA F 2) * (g * TR.infGL F 2 (c p.2)) :=
    (hu.comp continuous_fst).mul (continuous_const.mul ((ct_cont_infGL F 2).comp (hcc.comp continuous_snd)))
  have hper : ∀ ψ : GA F 2 → ℂ, (∀ γ g, ψ (ratGL F 2 γ * g) = ψ g) → ∀ γ ∈ ratN F 2 1, ∀ (x : NA F) (h : GA F 2),
      ψ (unip (γ + x) * h) = ψ (unip x * h) := by
    rintro ψ hψ _ ⟨y, rfl⟩ x h
    rw [hx, hx x]
    refine Eq.trans ?_ (hψ (aff 1 (y ⟨(0, 1), by decide⟩)) _)
    rw [← mul_assoc, ← ct_aff_add]
    rfl
  have key := hD (NA F) (ratN F 2 1) hco μ D hfin
    (fun x t => φ.1 (unip x * (g * TR.infGL F 2 (c t))))
    (fun x t => (TR.lie F 2 X φ).1 (unip x * (g * TR.infGL F 2 (c t))))
    (hc.comp hcont) (hc'.comp hcont)
    (fun γ hγ x => funext fun t => hper _ hl γ hγ x _)
    (fun γ hγ x => funext fun t => hper _ hl' γ hγ x _)
    (fun x t => by
      have h1 := TR.hasDerivAt_curve φ (unip x * (g * TR.infGL F 2 (c t))) c X h0 hder
      have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
      have h3 := HasDerivAt.scomp_of_eq t h1 h2 (sub_self t).symm
      rw [one_smul] at h3
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply, mul_assoc, ← map_mul, ← hmul, add_sub_cancel])
  simpa only [cterm, h0, map_one, mul_one] using key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousMixFamily
section
noncomputable section

open UpperTheory.V.Sd.S2 ReciprocityTheory.Gal

namespace UpperTheory

private theorem mix_cont {k X : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [TopologicalSpace X] (γ : kˣ)
    {A B : X → Matrix (Fin 2) (Fin 2) k} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => mix γ (A x) (B x) := by
  have a : ∀ i j, Continuous fun x => A x i j := fun i j => hA.matrix_elem i j
  have b : ∀ i j, Continuous fun x => B x i j := fun i j => hB.matrix_elem i j
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [mix, div_eq_mul_inv] <;> fun_prop

theorem continuous_mix_family : UpperTheory.V.Sd.S2.MixCont := by
  intro l _ Γ₀ Γ _ _ _ _ _ j t α β ρ R hM hj hρ
  haveI hN : j.range.Normal := Subgroup.normal_of_index_eq_two hM.index
  have hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := fun h => by
    have := hN.conj_mem (j h) ⟨h, rfl⟩ t⁻¹
    simpa using this
  choose c hc using hc
  have cc : Continuous c := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ c) = fun h => t⁻¹ * j h * t := funext hc
    rw [this]
    have := hj.continuous
    fun_prop
  have ci : Continuous fun h : Γ₀ => h⁻¹ := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ fun h : Γ₀ => h⁻¹) = fun h => (j h)⁻¹ := funext fun h => by simp
    rw [this]
    exact hj.continuous.inv
  have hv : Continuous fun h => (ρ h).val := Units.continuous_val.comp hρ
  have h1 : Continuous fun h => (R (j h)).val := by
    have : (fun h => (R (j h)).val) = fun h => mix (β / α) (ρ h) (ρ (c h)) :=
      funext fun h => hM.on h (c h) (hc h)
    rw [this]
    exact mix_cont _ hv (hv.comp cc)
  have h2 : Continuous (R ∘ j) := by
    rw [Units.continuous_iff]
    refine ⟨h1, ?_⟩
    have := h1.comp ci
    refine this.congr fun h => ?_
    simp only [Function.comp, map_inv]
  refine continuous_of_continuousAt_one R ?_
  have := (hj.continuousAt_iff (g := R) (x := 1)).1 h2.continuousAt
  rwa [map_one] at this

end UpperTheory
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharPowNTrivial
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (s : G ℚ Ω)
    (hs : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : UpperTheory.V.Chr.cls ℚ Ω N s = 1 := by
  have hcs := UpperTheory.V.Chr.cls_spec (k := ℚ) (Ω := Ω) N s
  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : NeZero (N : Ω) := ⟨by exact_mod_cast NeZero.ne N⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
    have h1 : ζ ^ 1 = ζ ^ (UpperTheory.V.Chr.cls ℚ Ω N s : ZMod N).val := by
      rw [pow_one, ← hcs ζ hζ.pow_eq_one, hs ζ hζ.pow_eq_one]
    have hv := hζ.pow_inj hN (ZMod.val_lt _) h1
    haveI : Fact (1 < N) := ⟨hN⟩
    apply Units.ext
    rw [Units.val_one]
    apply ZMod.val_injective
    rw [ZMod.val_one, ← hv]
  · have hN1 : N = 1 := by
      have := NeZero.pos N
      omega
    subst hN1
    exact Subsingleton.elim _ _

theorem UpperTheory.cyclotomicChar_pow_N_trivial :
    UpperTheory.V.Sd.S3.KillsN := by
  intro Ω _ _ _ l _ c D hD
  unfold Ctx3 at hD
  obtain ⟨hg, h, t, e, ψ, hb, he0, het, hX, hIII, hA⟩ := hD
  cases hA with
  | mk he hpsi hS hxi =>
  obtain ⟨x, ξ', ξ₀, -, -, -, hξ⟩ := hxi
  have hl2 : l ≠ 2 := UpperTheory.V.GradeZeroInterpolatingElement.Raw.Good.l_odd hg
  have hlp : Nat.Prime l := Fact.out
  unfold Host.CaseIII at hIII
  have hne : l ≠ UpperTheory.V.pOne h.chi :=
    ((UpperTheory.V.HV.bchiFacts h t hb).2.2.2.2 l hlp hl2 hIII.1).2.2.2.2.2.1
  have hP : Nat.Prime (UpperTheory.V.pOne h.chi) := (UpperTheory.V.pK_pOne_prime_conditions h.chi).2.1.1
  refine ⟨UpperTheory.V.pOne h.chi * 2 ^ h.nIII l ψ, Nat.mul_pos hP.pos (by positivity), ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hlp).1 hd with h1 | h1
    · exact hne ((Nat.prime_dvd_prime_iff_eq hlp hP).1 h1)
    · exact hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 (hlp.dvd_of_dvd_pow h1))
  · unfold KillsMu
    intro s hs
    have key : ∀ (M : ℕ) [NeZero M], M ∣ UpperTheory.V.pOne h.chi * 2 ^ h.nIII l ψ →
        UpperTheory.V.Chr.cls ℚ Ω M s = 1 := by
      intro M _ hM
      refine cls_one M s (fun ζ hζ => hs ζ ?_)
      obtain ⟨k, hk⟩ := hM
      rw [hk, pow_mul, hζ, one_pow]
    rw [hξ, MonoidHom.mul_apply]
    simp only [UpperTheory.V.Chr.dirG, MonoidHom.comp_apply]
    rw [key _ (dvd_mul_right _ _), key _ (dvd_mul_left _ _), map_one, map_one, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinCentralLieAction
section
open UpperTheory.V.Sd.Eis

theorem UpperTheory.eisenstein_central_lie_action :
    UpperTheory.V.Sd.Eis.CentLie :=
  fun F _ _ _ _ _ ω hω φ hφ v => UpperTheory.V.Sd.Hm.trzero F ω hω φ hφ.cent v
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermOfPeriodMeanOfUpperBlock
section
open UpperTheory.V.Sd.Eis

open UpperTheory.V.Sd in
private theorem cb_aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) :
    aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

open NumberField GlobalTheory.CuspRep UpperTheory.V.Sd in
private theorem cb_rat_aff (F : Type) [Field F] [NumberField F] (a : Fˣ) (y : F) :
    ratGL F 2 (aff a y) =
      aff (Units.map (algebraMap F (Ad F)).toMonoidHom a) (algebraMap F (Ad F) y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, ratGL]


open NumberField GlobalTheory.CuspRep in
private noncomputable def cb_scale (F : Type) [Field F] [NumberField F] (u : (Ad F)ˣ) : NA F ≃ₜ+ NA F where
  toFun x p := (u : Ad F) * x p
  invFun x p := ((u⁻¹ : (Ad F)ˣ) : Ad F) * x p
  left_inv x := funext fun p => Units.inv_mul_cancel_left u (x p)
  right_inv x := funext fun p => Units.mul_inv_cancel_left u (x p)
  map_add' x y := funext fun p => mul_add _ _ _
  continuous_toFun := continuous_pi fun p => continuous_const.mul (continuous_apply p)
  continuous_invFun := continuous_pi fun p => continuous_const.mul (continuous_apply p)

open NumberField GlobalTheory.CuspRep in
private theorem cb_mem (F : Type) [Field F] [NumberField F] (a : F) (x : NA F) (hx : x ∈ ratN F 2 1) :
    (fun p => algebraMap F (Ad F) a * x p) ∈ ratN F 2 1 := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => a * y p, funext fun p => map_mul (algebraMap F (Ad F)) _ _⟩

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock :
    UpperTheory.V.Sd.Eis.PerMean → UpperTheory.V.Sd.Eis.BlockTop → UpperTheory.V.Sd.Eis.CtBasic := by
  intro hM hB F _ _ _ _ μ _ D hF φ hc hl
  obtain ⟨i1, i2, i3, i4, hco, hu, hx⟩ := hB F
  have hper : ∀ (h : GA F 2), ∀ γ ∈ ratN F 2 1, ∀ x : NA F, φ (unip (γ + x) * h) = φ (unip x * h) := by
    rintro h _ ⟨y, rfl⟩ x
    rw [hx, hx x]
    refine Eq.trans ?_ (hl (aff 1 (y ⟨(0, 1), by decide⟩)) _)
    rw [← mul_assoc, cb_rat_aff, cb_aff_mul, map_one, one_mul, Units.val_one, one_mul, add_comm (x _)]
    rfl
  have key := fun g : GA F 2 =>
    (hM (NA F) (ratN F 2 1) hco μ D hF).2 (fun x => φ (unip x * g)) (hper g)
  refine ⟨fun g => (key g).1 (hc.comp (hu.mul continuous_const)), fun y g => ?_, fun a g => ?_⟩
  · unfold cterm
    refine Eq.trans ?_ ((key g).2.1 fun _ => y)
    refine congrArg (integral (μ.restrict D)) (funext fun x => ?_)
    rw [hx, hx, ← mul_assoc, cb_aff_mul, one_mul, Units.val_one, one_mul, add_comm y]
    rfl
  · let u : (Ad F)ˣ := Units.map (algebraMap F (Ad F)).toMonoidHom a
    unfold cterm
    refine Eq.trans ?_ ((key g).2.2 (cb_scale F u⁻¹) fun x => ⟨fun h => ?_, fun h => cb_mem F ((a⁻¹ : Fˣ) : F) x h⟩)
    · refine congrArg (integral (μ.restrict D)) (funext fun x => ?_)
      refine Eq.trans ?_ (hl (aff a 0) _)
      rw [hx, hx, cb_rat_aff, map_zero, ← mul_assoc, ← mul_assoc, cb_aff_mul, cb_aff_mul, one_mul, mul_one,
        mul_zero, zero_add, add_zero]
      change φ (aff u _ * g) = φ (aff u ((u : Ad F) * (((u⁻¹ : (Ad F)ˣ) : Ad F) * x _)) * g)
      rw [Units.mul_inv_cancel_left]
    · have h2 := cb_mem F (a : F) _ h
      have e : (fun p => algebraMap F (Ad F) (a : F) * cb_scale F u⁻¹ x p) = x :=
        funext fun p => Units.mul_inv_cancel_left u (x p)
      rwa [e] at h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermUpperBlock
section
open UpperTheory.V.Sd.Eis

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
private theorem cont_nilM (F : Type) [Field F] [NumberField F] :
    Continuous (fun x : NA F => (nilM x : Matrix (Fin 2) (Fin 2) (Ad F))) := by
  refine continuous_matrix fun i j => ?_
  simp only [nilM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
theorem UpperTheory.eisenstein_constantTerm_upperBlock :
    UpperTheory.V.Sd.Eis.BlockTop := by
  intro F _ _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact (Set.countable_range _).to_subtype
  · obtain ⟨C, hC, hx⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
    have hD : IsCompact (C ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :
        Set (Ad F)) := hC.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F)
    refine ⟨_, isCompact_univ_pi fun _ : BlockIx 2 1 => hD, fun x => ?_⟩
    choose k hk using hx
    exact ⟨fun p => algebraMap F (Ad F) (k (x p)), ⟨fun p => k (x p), rfl⟩, fun p _ => hk (x p)⟩
  · exact Units.continuous_iff.2 ⟨continuous_const.add (cont_nilM F), continuous_const.sub (cont_nilM F)⟩
  · intro x
    refine Units.ext ?_
    change 1 + nilM x = !![((1 : (Ad F)ˣ) : Ad F), x ⟨(0, 1), by decide⟩; 0, 1]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [nilM]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinLieAlgebraAction
section
open UpperTheory.V.Sd.Eis

private theorem complex_linear_combination_eq_half_of_relations (a b c d e f x y z w κ : ℂ) (hc : c - Complex.I * d ≠ 0)
    (h1 : a * e + b * f = 1) (h2 : c * e + d * f = 0)
    (hp1 : x + w = 0) (hp2 : y - z = Complex.I * κ) (hp3 : x - w = Complex.I * (y + z))
    (hE : e * (c * x + d * y) + f * (c * z + d * w) = 0) :
    e * (a * x + b * y) + f * (a * z + b * w) = κ / 2 := by
  have hw : w = -x := by linear_combination hp1
  have hs : y + z = -2 * Complex.I * x := by
    linear_combination (norm := skip) (Complex.I) * hp3 + (Complex.I) * hp1
    ring_nf; simp only [Complex.I_sq]; ring_nf
  have hy : y = -Complex.I * x + Complex.I * κ / 2 := by
    linear_combination (1/2) * hs + (1/2) * hp2
  have hz : z = -Complex.I * x - Complex.I * κ / 2 := by
    linear_combination (1/2) * hs - (1/2) * hp2
  subst hw hy hz
  apply mul_left_cancel₀ hc
  linear_combination (norm := skip) (a - Complex.I * b) * hE
    + (-κ/2) * (Complex.I * d - c) * h1 + (-κ/2) * (a - Complex.I * b) * h2
  ring_nf; simp only [Complex.I_sq, Complex.I_pow_four]; ring_nf

theorem UpperTheory.eisenstein_lie_algebra_action :
    UpperTheory.V.Sd.Eis.LieAlg := by
  intro h p κ hp1 hp2 hp3 hE
  have hMN : (h : Matrix (Fin 2) (Fin 2) ℝ) * ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1 := congrFun (congrFun hMN 0) 0
  have e2 := congrFun (congrFun hMN 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e1 e2
  have hdet : (h : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hMN
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [Matrix.det_fin_two] at hdet
  have hc : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) - Complex.I * ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp at hre him
    apply hdet
    rw [hre, him]; ring
  have hent : ∀ (k i j : Fin 2),
      (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.single (0 : Fin 2) k (1 : ℝ)
        * (h : Matrix (Fin 2) (Fin 2) ℝ)) i j
        = ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) k j := by
    intro k i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  simp only [hent, Fin.sum_univ_two, Complex.ofReal_mul] at hE ⊢
  have e1' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 1 := by
    exact_mod_cast e1
  have e2' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 0 := by
    exact_mod_cast e2
  have := complex_linear_combination_eq_half_of_relations _ _ _ _ _ _ (p 0 0) (p 0 1) (p 1 0) (p 1 1) κ hc e1' e2' hp1 hp2 hp3
    (by linear_combination hE)
  linear_combination this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinNormEqAbsPow
section
open UpperTheory.V.Sd.Eis NumberField GlobalTheory.Mem.Chr.CharModel

theorem UpperTheory.eisenstein_norm_eq_abs_pow :
    UpperTheory.V.Sd.Eis.AbsPow := by
  intro F _ _ _ s
  have H := absChar_isAbsPow (F := F) s
  refine ⟨⟨absHom F s, (absChar F s).2⟩, fun y hy => ?_, fun w => ⟨H.1 w, ?_⟩⟩
  · change Complex.exp (s * logNorm F (UpperTheory.V.TR.infId F y)) = _
    have h1 : finPart F (UpperTheory.V.TR.infId F y) = 1 := by
      apply Units.ext
      change (UpperTheory.V.TR.infId F y).val.2 = 1
      change ((1 : AdeleRing (𝓞 F) F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val).2 = 1
      change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) - 0 + 0 = 1
      simp
    have h2 : (infPart F (UpperTheory.V.TR.infId F y)).val = UpperTheory.V.TR.infEq F y.val := by
      change ((1 : AdeleRing (𝓞 F) F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val).1 = _
      change (1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F y.val = _
      simp
    have h3 : ∀ w : InfinitePlace F, ‖UpperTheory.V.TR.infEq F y.val w‖ = y.val w := fun w => by
      have := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.isometry.dist_eq (y.val w) 0
      have e0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 = 0 :=
        map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      rw [e0, dist_zero_right, dist_zero_right, Real.norm_of_nonneg (hy w).le] at this
      exact this
    rw [logNorm, h1, logFin_one, sub_zero, logInf, h2]
    simp only [h3, InfinitePlace.mult, IsTotallyReal.isReal, if_true, Nat.cast_one, one_mul]
    rw [← Real.log_prod (fun w _ => (hy w).ne'), Real.rpow_def_of_pos (Finset.prod_pos fun w _ => hy w),
      Complex.ofReal_exp, Complex.ofReal_mul, mul_comm]
  · refine (H.2.1 w).trans ?_
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticCharacterOfSubgroupIndexTwo
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd.S2

private theorem exists_sign_character_index_two {Γ R : Type} [Group Γ] [CommRing R] (H : Subgroup Γ) (h : H.index = 2) :
    ∃ φ : Γ →* Rˣ, (∀ g ∈ H, φ g = 1) ∧ ∀ g ∉ H, φ g = -1 := by
  classical
  refine ⟨MonoidHom.mk' (fun g => if g ∈ H then 1 else -1) fun a b => ?_, fun g hg => if_pos hg, fun g hg => if_neg hg⟩
  by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [Subgroup.mul_mem_iff_of_index_two h, ha, hb]

theorem UpperTheory.exists_quadratic_character_of_subgroup_index_two :
    UpperTheory.V.Sd.S2.HypEx := by
  intro Ω _ _ _ l _ c D T hg hok htwo hdeep
  obtain ⟨k₀, hdeg, hreal, hsp, hps⟩ := htwo.quad
  haveI : FiniteDimensional ℚ k₀ := Module.finite_of_finrank_pos (by omega)
  haveI hnf : NumberField k₀ := {}
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
  obtain ⟨hE, hO, hI⟩ := galEmbTop ℚ k₀ Ω
  have hfix : galOf ℚ k₀ Ω = k₀.fixingSubgroup := by
    ext σ
    rw [mem_galOf, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
  have hr : (resQ k₀).range = k₀.fixingSubgroup := (range_galEmb ℚ k₀ Ω).trans hfix
  have hidx : k₀.fixingSubgroup.index = 2 := by rw [← hfix, hI, hdeg]
  obtain ⟨φ, h1, h2⟩ := exists_sign_character_index_two (R := PadicAlgCl l) k₀.fixingSubgroup hidx
  refine ⟨k₀, hnf, hreal, φ, ⟨hg, hok, htwo, hdeep, hdeg, ?_, ?_, hps, h1, h2⟩, hr, hidx, hE, ?_⟩
  · exact hsp 2 (by simp)
  · exact hsp l (by simp)
  · rw [← MonoidHom.coe_range, hr, ← hfix]
    exact hO
end

