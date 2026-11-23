module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep GlobalTheory.CuspRep.LocEx
open GlobalTheory.CuspRep (SmIrr Af locGL pLoc finGL)
namespace UpperTheory.V.Af.RealLocalComponent
section Gen
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
private def orb (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x
private theorem orb_comm (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
    (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]
private theorem orb_act (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
    orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
  | single a b => simp [orb]
private def annPart (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V where
  carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
  add_mem' := fun {x y} hx hy c hc => by
    have : orb κ (x + y) c = orb κ x c + orb κ y c := by
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
    rw [this, hx c hc, hy c hc, add_zero]
  zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
  smul_mem' := fun a x hx c hc => by
    have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
    simpa [hx c hc] using this
private theorem exists_type (κ : Representation ℂ K V) (φ : V)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
    ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
      (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
  have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨_, orb_act κ φ k c⟩
  haveI : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
    rw [orb, Finsupp.range_linearCombination]; exact hφ
  let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
  obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
  have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
    rw [← sub_eq_zero, ← map_sub]
    refine hx _ ?_
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
  refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
    ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
  · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
    obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
    have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
        b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
      have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
        Subtype.ext (orb_act κ φ k c)
      rw [h2]
      exact LinearMap.toMatrix_mulVec_repr b b _ _
    rw [h1]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
    simp [orb]
end Gen
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}
private theorem smooth_fin (π : TR.CuspSub F n) : IsSmooth π.finPart := fun v => by
  convert (π.cusp v.1 v.2).1.level using 1
  ext k
  exact Subtype.ext_iff
private theorem smooth_loc (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) : IsSmooth (π.locRep w) := fun v =>
  (smooth_fin π v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)
private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]
private theorem fin_loc (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)}
    (hk : GeneralLinearGroup.map (pLoc F w) k = 1) (g : GL (Fin n) (w.adicCompletion F)) (y : π.V) :
    π.finPart k (π.locRep w g y) = π.locRep w g (π.finPart k y) := by
  simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w hk]
private theorem bot_or_top (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (W : Submodule ℂ π.V)
    (h1 : ∀ g, ∀ x ∈ W, π.locRep w g x ∈ W)
    (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ W, T x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
    cases o with
    | fin k =>
      have h3 := h1 (GeneralLinearGroup.map (pLoc F w) k) _ (h2
        (π.finPart ((locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ * k))
        (fin_loc π w (map_pLoc_inv_mul w k)) x hx)
      rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h3
    | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
    | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F n w g)) y.1)) x hx
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h | h
  · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))
private theorem isotypic (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (h : π.IsLocComp w σ) : LocIsotypic π.finPart w σ := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  refine (bot_or_top π w _ (fun g x hx => ?_) (fun T hT x hx => ?_)).resolve_left fun e => ?_
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep w g) _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
      rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨v, rfl⟩
  · obtain ⟨f, h0, hf⟩ := h
    exact h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩))
private def cptPart (π : TR.CuspSub F n) : Representation ℂ (TR.Kinf F n) π.V :=
  sub (TR.cptRep F n) π.V fun k => π.stable (.cpt k)
private theorem exists_comp (h : UpperTheory.V.Published.AdmissibleReal) (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) :
    ∃ σ, π.IsLocComp w σ := by
  obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ : π.V := ⟨φ₀, hφ⟩
  have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  set L := stab π.finPart φ
  have hL : IsOpen (L : Set (GL (Fin n) (Af F))) := smooth_fin π _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
    have := (π.cusp φ₀ hφ).1.kfin
    refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
      (Submodule.span ℂ (Set.range fun k => TR.cptRep F n k φ₀)) fun v => ?_)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
  have hcomm : ∀ g k x, π.finPart g (cptPart π k x) = cptPart π k (π.finPart g x) := fun g k x => (cpt_fin π k g x).symm
  let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓
    fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin n) (pLoc F w)).ker)
  obtain ⟨σ, hσ, -⟩ := exists_irred (smooth_loc π w) ho (fun W hW e => by
      rcases bot_or_top π w (nullPart (π.locRep w) K) (fun g x hx => nullPart_act _ K g hx)
        (fun T hT x hx => nullPart_comm _ K T hT hx) with h2 | h2
      · exact le_bot_iff.1 (h2 ▸ le_nullPart (smooth_loc π w) hc W hW e)
      · exact absurd (eq_zero_of_mem_nullPart (smooth_loc π w) hc (mem_fix.2 hK) (h2 ▸ Submodule.mem_top)) h0')
    U (fun g x hx => ⟨fun c hc => by
        rw [TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
      mem_fix.2 fun k hk => by rw [fin_loc π w hk.2, mem_fix.1 hx.2 k hk]⟩)
    ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, h0'⟩) (fun K' hK' => by
      obtain ⟨W, hW, hWf⟩ := h F n π (L ⊓ (K' ⊓ L.comap (locGL F n w)).comap (GeneralLinearGroup.map (pLoc F w)))
        (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w))).preimage
          (continuous_map_pLoc w))) d ξ
      refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
      obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
      refine hWf f hf (fun k hk v => ?_) hx1
      have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul w k⟩
      have h2 := mem_fix.1 hx.2 _ hk.2.1
      have h3 : π.finPart k x = x := by
        rw [← mul_inv_cancel_left (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) k, map_mul,
          Module.End.mul_apply, h1]
        exact h2
      obtain ⟨c, hc⟩ := hf2 v
      rw [hc, ← orb_comm _ _ (hcomm k), h3])
  exact ⟨σ, hσ⟩
end UpperTheory.V.Af.RealLocalComponent
theorem UpperTheory.V.Af.local_comp_real_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.LocCompR := fun P _ _ _ _ _ π w =>
  ⟨UpperTheory.V.Af.RealLocalComponent.exists_comp P.admR π w, UpperTheory.V.Af.RealLocalComponent.isotypic π w⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TRegElt
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem regElt_place {Ω : Type} [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hI : Ideal.span {((p : ℕ) : (Int.castRingHom Ω).range)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨_, c, rfl⟩, hc⟩
    have h1 : ((p : ℕ) : Ω) * ((c : ℤ) : Ω) = 1 := congrArg Subtype.val hc
    have h2 : ((p : ℕ) : ℤ) * c = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
    exact hp.one_lt.ne' (by exact_mod_cast h3)
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : (Int.castRingHom Ω).range), Ideal.mem_span_singleton_self _, by simp⟩)⟩
private theorem regElt_zpow_ne {G : Type} [Group G] (e : G) (he : ¬ IsOfFinOrder e) (n : ℤ) (hn : 0 < n) : e ^ n ≠ 1 := by
  intro h
  refine he (isOfFinOrder_iff_pow_eq_one.2 ⟨n.toNat, by omega, ?_⟩)
  rw [← zpow_natCast, Int.toNat_of_nonneg hn.le, h]
private theorem regElt_key {K : Type} [Field K] (e x : Kˣ) (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k)
    (hx : x ^ k = (e ^ (m : ℤ)) ^ k) (he : ¬ IsOfFinOrder e) :
    ¬ IsOfFinOrder x ∧ ∀ i : ℤ, |i| ≤ 2 →
      ((x : K) + ((x⁻¹ : Kˣ) : K)) ^ 2 - 2 ≠ (e : K) ^ i + (e : K) ^ (-i) := by
  have hsq : ∀ j : ℤ, |j| ≤ 2 → x ^ 2 ≠ e ^ j := by
    intro j hj h
    have hj' := (abs_le.1 hj).2
    have hpos : 0 < (2 * (m : ℤ) - j) * (k : ℤ) := by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      have : (2 : ℤ) ≤ m := by exact_mod_cast hm
      apply mul_pos <;> omega
    refine regElt_zpow_ne e he _ hpos ?_
    have h1 : (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k = (e ^ j) ^ k := by
      rw [← hx, ← h, ← pow_add, ← pow_mul, two_mul]
    have h2 : e ^ ((2 * (m : ℤ) - j) * (k : ℤ)) = (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k * ((e ^ j) ^ k)⁻¹ := by
      simp only [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    rw [h2, h1, mul_inv_cancel]
  refine ⟨fun hf => ?_, fun i hi h => ?_⟩
  · obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    have hpos : 0 < (m : ℤ) * k * n := by
      have a : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
      have b : (0 : ℤ) < k := by exact_mod_cast hk
      have c : (0 : ℤ) < n := by exact_mod_cast hn
      positivity
    refine regElt_zpow_ne e he _ hpos ?_
    rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← hx, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  · have hx0 : (x : K) ≠ 0 := x.ne_zero
    have hE0 : ((e : K) ^ i) ≠ 0 := zpow_ne_zero _ e.ne_zero
    have hz : ((x : K) ^ 2 - (e : K) ^ i) * ((x : K) ^ 2 - ((e : K) ^ i)⁻¹) = 0 := by
      rw [Units.val_inv_eq_inv_val, zpow_neg] at h
      field_simp at h ⊢
      linear_combination (exp := 1) h
    rcases mul_eq_zero.1 hz with h0 | h0
    · refine hsq i hi (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
      exact sub_eq_zero.1 h0
    · refine hsq (-i) (by rwa [abs_neg]) (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, zpow_neg]
      exact sub_eq_zero.1 h0
theorem UpperTheory.V.Z.Sym.Ga.exists_regular_elt_in_open_subgroup_infinite_order :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)), _root_.UpperTheory.V.Z.Sym.AdInAlt ι M m r → ∀ H : Subgroup (G L Ω), IsOpen (H : Set (G L Ω)) → ∃ s ∈ H, s ∉ Ga.Bad r ∧ ∃ a b : (Qbar l)ˣ, ¬ IsOfFinOrder (a / b) ∧ (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l)) := by
  intro L Ω _ _ _ _ _ _ l _ ι M m r hr H hH
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨A, hA⟩ := regElt_place (Ω := Ω) l (Fact.out)
  obtain ⟨b0, k, κ, hk, ⟨g, hg⟩, hκ⟩ := hr.above A hA
  obtain ⟨s, hsH, hsI, hinf⟩ := UpperTheory.V.Z.Sym.Ga.ineInf L Ω l A hA H hH
  let t : ↥(Dec (F := L) A) := ⟨s, Ine_le_Dec A hsI⟩
  obtain ⟨h0, h1⟩ := hκ t hsI
  have hcp : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C ((κ 0 t : (Qbar l)ˣ) : Qbar l)) * (X - C ((κ 1 t : (Qbar l)ˣ) : Qbar l)) := by
    have e : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
        (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj g _
    rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (hg t).1 i j hij), Fin.prod_univ_two]
    have e0 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((κ 0 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 0
    have e1 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = ((κ 1 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 1
    rw [e0, e1]
  have hx : (κ 0 t / κ 1 t) ^ k = (cycBar L Ω l s ^ (m : ℤ)) ^ k := by
    rw [div_pow, h0, h1, zpow_add, mul_pow]
    exact mul_div_cancel_left _ _
  have key := regElt_key (cycBar L Ω l s) (κ 0 t / κ 1 t) m k hr.gap hk hx hinf
  refine ⟨s, hsH, ?_, κ 0 t, κ 1 t, key.1, hcp⟩
  rintro ⟨i, hi, hb⟩
  have huf := (UpperTheory.V.Z.Sym.Ga.ufFacts _ (r s)).1 _ _ hcp
  rw [huf] at hb
  exact key.2 i hi hb
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep
theorem UpperTheory.V.Af.satake_local_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.SatLoc := by
  intro _ F _ _ n w σ
  have hex : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w (n := n)) → ∃ B, HasSatGL w σ.ρ B :=
    GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
  refine ⟨fun ⟨v, h0, hv⟩ => hex ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩), ?_⟩
  intro V _ _ ρ ⟨hV, htop⟩ B
  have up : ∀ B, HasSatGL w σ.ρ B → HasSatGL w (ρ.comp (locGL F n w)) B := by
    intro B h
    constructor
    · obtain ⟨f, h0⟩ : ∃ f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)}, f.1 ≠ 0 := by
        by_contra hc
        push Not at hc
        refine top_ne_bot (htop.symm.trans (eq_bot_iff.2 (iSup_le fun f => ?_)))
        rw [hc f, LinearMap.range_zero]
      obtain ⟨x, hx⟩ := h.exists_vec
      have hi : LinearMap.ker f.1 = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [f.2, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
      have h1 := hx.map (ρ' := ρ.comp (locGL F n w)) f.1 f.2
        ((map_ne_zero_iff f.1 (LinearMap.ker_eq_bot.1 hi)).2 hx.1)
      exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
    · intro x hx h0
      exact GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := ρ.comp (locGL F n w)) σ.irred h
        (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)} => f.1) (fun f => f.2)
        (htop ▸ Submodule.mem_top) hx h0
  refine ⟨fun h => ?_, up B⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h.1
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup (ρ.comp (locGL F n w)) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)} => f.1) (fun f => f.2)
    (KGL w (n := n) : Set _) x hx0 (fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk) (htop ▸ Submodule.mem_top)
  obtain ⟨B', hB'⟩ := hex ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
  exact (up B' hB').unique h ▸ hB'
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TToCsd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Matrix
private theorem eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M M' P : GL (Fin n) K) (t : K)
    (hP : (M : Matrix (Fin n) (Fin n) K)ᵀ * (P : Matrix (Fin n) (Fin n) K) * (M' : Matrix (Fin n) (Fin n) K) =
      t • (P : Matrix (Fin n) (Fin n) K)) (S S' : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod)
    (h' : (M' : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S'.map fun b => X - C b).prod) :
    S = S'.map fun a => φ t * a⁻¹ := by
  have h0 : (M : Matrix (Fin n) (Fin n) K)ᵀ = (P : Matrix (Fin n) (Fin n) K) *
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hP, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have h1 : (M : Matrix (Fin n) (Fin n) K).charpoly =
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly := by
    rw [← Matrix.charpoly_transpose, h0, Matrix.coe_units_inv P, Matrix.charpoly_units_conj]
  rw [← Matrix.charpoly_map] at h'
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M') (φ t) _ h'
  have h4 : (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M')⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [h1, ← Matrix.charpoly_map, h4, h3] at h
  have h5 := congrArg roots h
  rw [roots_multiset_prod_X_sub_C] at h5
  rw [← roots_multiset_prod_X_sub_C (S'.map fun a => φ t * a⁻¹), Multiset.map_map]
  exact h5.symm
private theorem cPl_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    cPl w = preplace (IsCMField.complexConj E).toRingEquiv w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))
private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm
private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))
private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)
private theorem frob_dual {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {θ : G F Ω →* (Qbar l)ˣ}
    {c : G (maximalRealSubfield F) Ω} {P : GL (Fin n) (Qbar l)} (hc : IsConjEl c)
    (hP : IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * θ) P) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {B B' : Multiset ℂˣ} {z : ℂˣ} (hB : FrobEig ι r w (algSat n (normV w) B))
    (hB' : FrobEig ι r (cPl w) (algSat n (normV (cPl w)) B')) (hz : CharEig ι θ w z) :
    B'.map (·⁻¹) = B.map (· * z⁻¹) := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have hL := isLift_conj hc
  have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
  rw [cPl_eq] at hB'
  have e := (hB' _ (isPlaceOver_preplace hL hAA hA)).2 (conjGal hL σ)
    (by rw [normV_preplace]; exact isFrob_conjGal hL hAA hσ)
  rw [normV_preplace] at e
  have h1 := eig_dual ι.toRingHom (r σ⁻¹) (r (conjGal hL σ)⁻¹) P _
    (hP σ⁻¹ (conjGal hL σ)⁻¹ (by rw [← map_inv]; exact AlgEquiv.ext fun _ => rfl)) _ _ ((hB A hA).2 σ hσ) e
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have h3 := (hz A hA).2 σ hσ
  set d : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hdd : d * d = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hd, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom (((cycBar F Ω l ^ (1 - (n : ℤ)) * θ) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = d * d * z := by
    change ι _ = _
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, map_inv (cycBar F Ω l),
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, h3, hdd, inv_zpow',
      neg_sub]
  have hS : ∀ B : Multiset ℂˣ, algSat n (normV w) B = B.map fun α : ℂˣ => d * (α : ℂ) := fun B => by
    simp only [algSat, ← hd, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [h4, hS, hS] at h1
  have h5 := congrArg (Multiset.map fun a : ℂ => d⁻¹ * a * (z : ℂ)⁻¹) h1
  simp only [Multiset.map_map, Function.comp_def] at h5
  apply Multiset.map_injective (f := (Units.val : ℂˣ → ℂ)) Units.val_injective
  simp only [Multiset.map_map, Function.comp_def]
  have := z.ne_zero
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (h5.symm.trans (Multiset.map_congr rfl fun a _ => ?_))
  · rw [Units.val_inv_eq_inv_val]
    have := a.ne_zero
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
theorem selfDual_of_automorphic_inputs :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.SelfDualC := by
  intro H F Ω _ _ _ _ _ _ l _ ι n hn r π hπ χ μ hμ c P hc hP
  refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse H.litN.aut.js.1 H.litN.aut.gk F n hn π _ ?_
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have h2 := (conjSrc_injective (IsCMField.complexConj F).toRingEquiv).tendsto_cofinite.eventually hπ.2
  filter_upwards [Bc.normGal F Ω l ι χ μ hμ, hπ.2, h2, hl] with w ⟨hu, he⟩ ⟨B, hB, hF⟩ ⟨B', hB', hF'⟩ hw
  exact ⟨hu, B, B', hB, hB', frob_dual hc hP hw hF hF' he⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistConjugateSelfDual
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af
private theorem isAlg_of_pos {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {κ : HChar K}
    {m : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ m) : κ.IsAlg m := fun k => hκ k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp
private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩
theorem UpperTheory.V.Sd.twist_conjugate_selfDual :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.TwC := by
  intro _ F Ω _ _ _ _ _ _ l _ ι n r κ ⟨_, art, χ, a, hart, hpos, hL⟩ ⟨π, hreg, hatt⟩
  exact ⟨π.twist χ, regAlg_twist hreg (isAlg_of_pos hpos),
    UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hatt art χ a κ hart hL⟩
end
end

