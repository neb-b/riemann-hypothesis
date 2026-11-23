module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.DefsBad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Ws UpperTheory.V.Cu UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open scoped Matrix

private theorem algPos_of_expo (ω : HChar ℚ) (h : ∀ v, ∃ n : ℤ, TR.expo ω v = n) : ∃ a, IsAlgPos ω a := by
  obtain ⟨n, hn⟩ := h default
  refine ⟨fun _ => n, fun k hk => ?_⟩
  letI : Unique (ℚ →+* ℂ) := ⟨⟨Rat.castHom ℂ⟩, fun _ => Subsingleton.elim _ _⟩
  have hk0 : (0 : ℝ) < ((k : ℚ) : ℝ) := hk (Rat.castHom ℝ)
  let diagR : ℚ →+* TR.Rinf ℚ := (TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ))
  have hv : ∀ v, diagR (k : ℚ) v = ((k : ℚ) : ℝ) := fun v =>
    eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp diagR) (k : ℚ)
  have e : Units.map diagR.toMonoidHom k = TR.expU fun _ => Real.log ((k : ℚ) : ℝ) :=
    Units.ext (funext fun v => (hv v).trans (Real.exp_log hk0).symm)
  have hdiag : infDiag k = TR.infId ℚ (Units.map diagR.toMonoidHom k) := by
    have h : ((infDiag k : Ideles ℚ) : AdeleRing (𝓞 ℚ) ℚ) = (algebraMap ℚ (InfiniteAdeleRing ℚ) k, 1) := by
      unfold infDiag
      rw [MonoidHom.finsetProd_apply, Fintype.prod_unique, MonoidHom.comp_apply]
      refine Prod.ext (funext fun w => ?_) rfl
      have hw : w = default := Subsingleton.elim _ _
      subst w
      exact ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self ℚ default (atInf default k)
    apply Units.ext
    rw [h]
    refine Prod.ext ?_ ?_
    · change _ = 1 - TR.infEq ℚ 1 + TR.infEq ℚ ((TR.infEq ℚ).symm (algebraMap ℚ (InfiniteAdeleRing ℚ) k))
      simp
    · change (1 : Af ℚ) = 1 - 0 + 0
      simp
  have e2 := TR.chiInf_expU_eq ω fun _ => Real.log ((k : ℚ) : ℝ)
  rw [← e, Fintype.sum_unique, hn, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hk0] at e2
  rw [HChar.inf, MonoidHom.comp_apply, hdiag, Fintype.prod_unique, eq_ratCast, ← Complex.ofReal_ratCast]
  exact e2

private theorem det_sat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = ((x * y : ℂˣ) : ℂ) * q := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C]
  simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_apply]
  rw [Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, mul_mul_mul_comm, hq', Units.val_mul, mul_comm]

private theorem det_alg (P : HypothesesH) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hc : Continuous ρ) (ha : IsAutR ι ρ) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp ρ) := by
  obtain ⟨π, hreg, hatt⟩ := ha
  obtain ⟨ω, hcentral, -⟩ := UpperTheory.V.Sd.Wc.centChar P.toClassicalTheorems ℚ π
  have hω : ∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w := by
    intro w α β hB
    obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
    have hZ := (UpperTheory.V.Br.uOfSat ℚ w _ _ x α β hx).2
    have hscalar (u : (w.adicCompletion ℚ)ˣ) :
        finGL ℚ 2 (locGL ℚ 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) (localIdele ℚ w u) := by
      have h := GlobalTheory.CuspRep.finId_det_locGL w (Matrix.GeneralLinearGroup.scalar (Fin 1) u)
      rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
      rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
      congr 1
      exact (congrArg (finId ℚ) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
        (h.trans (congrArg (localIdele ℚ w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))
    have haction : π.locRep w (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x =
        ((ω.val w : ℂˣ) : ℂ) • x := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      change x.1.1 (g * finGL ℚ 2 (locGL ℚ 2 w _)) = _
      rw [hscalar, ← GlobalTheory.CuspRep.scalar_comm, hcentral _ _ x.2]
      rfl
    exact Units.ext (smul_left_injective ℂ hx.1 (hZ.symm.trans haction))
  have hint : ∀ v, ∃ n : ℤ, TR.expo ω v = n := by
    intro v
    have hiso : π.Iso (π.dual.twist ω) := by
      refine P.toClassicalTheorems.smoR ℚ 2 one_le_two _ _ ?_
      filter_upwards [hatt.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ω)]
        with w ⟨B, hB, _⟩ hu
      obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 hB.card
      have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * ω.val w) = {α, β} := by
        rw [← hω w α β hB, Multiset.pair_comm α β]
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
        rw [mul_comm α β, inv_mul_cancel_left]
        exact Multiset.pair_comm α β
      exact ⟨_, hB, e ▸ hB.dual.twist hu⟩
    obtain ⟨m, hm, -, hz⟩ := hreg v
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hm.1
    obtain ⟨i, hi⟩ := hz x (by simp)
    obtain ⟨j, hj⟩ := hz y (by simp)
    have h := congrArg Multiset.sum ((hiso.hasInfChar hm).unique (hm.dual.twist ω))
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
      Multiset.sum_singleton] at h
    refine ⟨i + j + 1, ?_⟩
    push_cast at hi hj ⊢
    linear_combination hi + hj - h / 2
  obtain ⟨a, hal⟩ := algPos_of_expo ω hint
  obtain ⟨art, hart⟩ : ∃ art : Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art := P.toClassicalTheorems.litN.aut.art _ Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι hal
  have hch : IsCharOf ι ω μ := ⟨hμ, art, a, hart, hal, hL⟩
  obtain ⟨hcc, χ, art', a', h'⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic P.toClassicalTheorems.litN.aut.art ℚ Ω l ι 1 (cycBar ℚ Ω l)
    ⟨1, 1, le_rfl, fun _ _ => rfl, by rw [zpow_one, mul_one]⟩
  have H := (algOfCyc P ℚ Ω l ι).2.1
  have h1 : Af.IsAlgChar ι (cycBar ℚ Ω l) := ⟨χ, hcc, art', a', h'⟩
  have h2 := (H μ _ ⟨ω, hch⟩ (H _ _ h1 h1).2).1
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    have hl : l.Prime := Fact.out
    have h0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hl.ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
    exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have key : (fun s : G ℚ Ω => (ρ s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det) =
      fun s => (((μ * (cycBar ℚ Ω l)⁻¹) s⁻¹ : (Qbar l)ˣ) : Qbar l) := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 ((hatt.2.and (UpperTheory.galois_character_frobenius_compatibility ℚ Ω l ι ω μ hch)).and hl))
      (Units.continuous_val.comp (hc.comp continuous_inv)).matrix_det
      (Units.continuous_val.comp ((hμ.mul hcc.inv).comp continuous_inv)) ?_
    intro v hv _ A hA σ hσ
    obtain ⟨⟨⟨B, hB, hF⟩, -, h3⟩, h4⟩ := not_not.1 hv
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have hcyc : ι (((cycBar ℚ Ω l)⁻¹ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV v : ℂ) := by
      have hval : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob h4 hA hσ, map_natCast, map_natCast]
      rw [MonoidHom.inv_apply, map_inv, inv_inv, hval, map_natCast]
    apply ι.injective
    rw [MonoidHom.mul_apply, Units.val_mul, map_mul, (h3 A hA).2 σ hσ, hcyc,
      ← hω v x y hB, ← det_sat _ _ _ _ e2]
    exact ι.toRingHom.map_det _
  have e : Matrix.GeneralLinearGroup.det.comp ρ = μ * (cycBar ℚ Ω l)⁻¹ := MonoidHom.ext fun s => Units.ext (by
    have := congrFun key s⁻¹
    simp only [inv_inv] at this
    exact this)
  rw [e]
  exact h2

private theorem conj_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩

private theorem conj_off {Ω : Type} [Field Ω] [CharZero Ω] (K' : IntermediateField ℚ Ω) (hK : IsTotallyComplex K') {c : G ℚ Ω}
    (hc : IsConjEl c) : c ∉ K'.fixingSubgroup := by
  intro h
  obtain ⟨j, hj⟩ := hc
  refine InfinitePlace.not_isReal_iff_isComplex.2 (hK.isComplex (InfinitePlace.mk (j.comp (algebraMap K' Ω))))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
  exact (hj x).symm.trans (congrArg j (h x))

private theorem pair_plane {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring

private theorem kap_anti {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {K' : IntermediateField ℚ Ω} [NumberField K'] {g0 : G ℚ Ω} {m : ℕ} {c₁ : Coef l} {κ : G K' Ω →* (Qbar l)ˣ}
    {τ : G ℚ Ω →* Sd.S3.M2 c₁.O} {s} (hτ : TauDat ι K' g0 m c₁ τ s κ) {c : G ℚ Ω} (hc : c ∉ K'.fixingSubgroup) {g g' : G K' Ω}
    (h : resQ K' g' = c * resQ K' g * c⁻¹) : (κ g : Qbar l) * κ g' = 1 := by
  have hf : ∀ x, τ x 0 0 ^ 2 - τ x 1 0 ^ 2 = 1 := fun x => by
    have h := congrFun (congrFun (hτ.form x) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have hg : resQ K' g ∈ K'.fixingSubgroup := fun y => g.commutes y
  have e : τ (resQ K' g') * τ c = τ c * τ (resQ K' g) := by
    rw [h, ← map_mul, ← map_mul, inv_mul_cancel_right]
  have hg' : resQ K' g' ∈ K'.fixingSubgroup := fun y => g'.commutes y
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 0) 1
  have f1 := hf c
  have f2 := hf (resQ K' g)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, (hτ.off c hc).1, (hτ.off c hc).2, (hτ.on _ hg).1, (hτ.on _ hg).2] at e0 e1 f1 f2
  have key : (τ (resQ K' g) 0 0 + τ (resQ K' g) 0 1) * (τ (resQ K' g') 0 0 + τ (resQ K' g') 0 1) = 1 := by
    generalize τ (resQ K' g) 0 0 = a at *
    generalize τ (resQ K' g) 0 1 = b at *
    generalize τ (resQ K' g') 0 0 = a' at *
    generalize τ (resQ K' g') 0 1 = b' at *
    generalize τ c 0 0 = p at *
    generalize τ c 0 1 = q at *
    linear_combination (a + b) * (p + q) * (e0 - e1) + f2 - (a + b) * (a' + b' - a + b) * f1
  rw [hτ.val g, hτ.val g']
  exact_mod_cast congrArg (fun z : c₁.O => (z : Qbar l)) key

end
