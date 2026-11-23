module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PureSt
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0003
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0004
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0002
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.Bundle0003
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.IndicatorMem

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.FiniteAdelicEstimatesHolds
section
noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo
  GlobalTheory.LatVac

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : Pl F}

def liftW (v : Pl F) (y : (κ → Fv F v) × (κ → Fv F v)) : (κ → AF F) × (κ → AF F) :=
  (fun i => liftV v (y.1 i), fun i => liftV v (y.2 i))

omit [Fintype κ] in
theorem locW_smul (a : AF F) (z : (κ → AF F) × (κ → AF F)) : locW v (a • z) = evFin F v a • locW v z :=
  Prod.ext (funext fun _ => map_mul _ _ _) (funext fun _ => map_mul _ _ _)

omit [Fintype κ] in
theorem locW_add (z z' : (κ → AF F) × (κ → AF F)) : locW v (z + z') = locW v z + locW v z' :=
  Prod.ext (funext fun _ => map_add _ _ _) (funext fun _ => map_add _ _ _)

omit [Fintype κ] in
theorem locW_liftW (y : (κ → Fv F v) × (κ → Fv F v)) : locW v (liftW v y) = y :=
  Prod.ext (funext fun _ => evFin_liftV _ _) (funext fun _ => evFin_liftV _ _)

omit [Fintype κ] in
theorem liftW_locW (z : (κ → AF F) × (κ → AF F)) : liftW v (locW v z) = liftV v 1 • z :=
  Prod.ext (funext fun _ => (GlobalTheory.LatVacArith.liftV_one_mul _ _).symm) (funext fun _ => (GlobalTheory.LatVacArith.liftV_one_mul _ _).symm)

def locT (v : Pl F) (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ((κ → Fv F v) × (κ → Fv F v)) →ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)) where
  toFun y := locW v (T (liftW v y))
  map_add' y y' := by
    rw [← locW_add, ← map_add (f := _)]
    congr 2
    exact Prod.ext (funext fun _ => map_add _ _ _) (funext fun _ => map_add _ _ _)
  map_smul' c y := by
    have e : liftW v (c • y) = liftV v c • liftW v y := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        exact ((mul_liftV _ _).trans (by rw [evFin_liftV]; rfl)).symm
    rw [e, map_smul, locW_smul, evFin_liftV]
    rfl

omit [Fintype κ] in
theorem locT_locW (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) (z) : locT v T (locW v z) = locW v (T z) := by
  change locW v (T (liftW v (locW v z))) = _
  rw [liftW_locW, map_smul, locW_smul, evFin_liftV, one_smul]

def locE (v : Pl F) (S : ((κ → AF F) × (κ → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ((κ → Fv F v) × (κ → Fv F v)) ≃ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)) :=
  { locT v S.toLinearMap with
    invFun := locT v S.symm.toLinearMap
    left_inv := fun y => by
      change locT v _ (locW v _) = _
      rw [locT_locW, LinearEquiv.coe_coe, LinearEquiv.coe_coe, S.symm_apply_apply, locW_liftW]
    right_inv := fun y => by
      change locT v _ (locW v _) = _
      rw [locT_locW, LinearEquiv.coe_coe, LinearEquiv.coe_coe, S.apply_symm_apply, locW_liftW] }

def intW (v : Pl F) : Submodule (v.adicCompletionIntegers F) ((κ → Fv F v) × (κ → Fv F v)) where
  carrier := {y | (∀ i, y.1 i ∈ v.adicCompletionIntegers F) ∧ ∀ i, y.2 i ∈ v.adicCompletionIntegers F}
  add_mem' ha hb := ⟨fun i => add_mem (ha.1 i) (hb.1 i), fun i => add_mem (ha.2 i) (hb.2 i)⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ h := ⟨fun i => mul_mem c.2 (h.1 i), fun i => mul_mem c.2 (h.2 i)⟩

theorem locW_int (z : (κ → AF F) × (κ → AF F)) : ∀ᶠ v in cofinite, locW v z ∈ intW v :=
  (eventually_all.2 fun i => (z.1 i).2.2).and (eventually_all.2 fun i => (z.2 i).2.2)

theorem locT_int (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ∀ᶠ v in cofinite, ∀ y ∈ intW v, locT v T y ∈ intW v := by
  classical
  filter_upwards [eventually_all.2 fun i => locW_int (T (Pi.single i 1, 0)), eventually_all.2 fun i => locW_int (T (0, Pi.single i 1))]
    with v h1 h2 y hy
  have e : liftW v y = ∑ i, liftV v (y.1 i) • ((Pi.single i 1, 0) : (κ → AF F) × (κ → AF F)) +
      ∑ i, liftV v (y.2 i) • ((0, Pi.single i 1) : (κ → AF F) × (κ → AF F)) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp [liftW, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hs : ∀ (c : κ → Fv F v) (z : κ → (κ → AF F) × (κ → AF F)), (∀ i, c i ∈ v.adicCompletionIntegers F) →
      (∀ i, locW v (T (z i)) ∈ intW v) → locW v (T (∑ i, liftV v (c i) • z i)) ∈ intW v := fun c z hc hz => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_induction _ (fun t => locW v t ∈ intW v) (fun a b ha hb => locW_add a b ▸ add_mem ha hb) ?_ fun i _ => ?_
    · have z0 : evFin F v 0 ∈ v.adicCompletionIntegers F := by rw [map_zero]; exact zero_mem _
      exact ⟨fun _ => z0, fun _ => z0⟩
    · rw [map_smul, locW_smul, evFin_liftV]
      exact ⟨fun j => mul_mem (hc i) ((hz i).1 j), fun j => mul_mem (hc i) ((hz i).2 j)⟩
  change locW v (T (liftW v y)) ∈ _
  rw [e, map_add (f := _), locW_add]
  exact add_mem (hs _ _ hy.1 h1) (hs _ _ hy.2 h2)

theorem schr_std {ψ : AddChar (AF F) ℂ} (hψ : PsiUnr ψ v) (h2 : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F) {y} (hy : y ∈ intW (κ := κ) v) :
    schr (psiV ψ v) y (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  funext x
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have h : psiV ψ v (x ⬝ᵥ y.2 + ⅟(2 : Fv F v) * (y.1 ⬝ᵥ y.2)) = 1 := by
      have := (hψ _).2 (show x ⬝ᵥ y.2 + ⅟(2 : Fv F v) * (y.1 ⬝ᵥ y.2) ∈ v.adicCompletionIntegers F from
        add_mem (sum_mem fun i _ => mul_mem (hx i) (hy.2 i))
          (mul_mem (by rwa [invOf_eq_inv]) (sum_mem fun i _ => mul_mem (hy.1 i) (hy.2 i)))) 1 (one_mem _)
      rwa [mul_one] at this
    rw [schr, h, one_mul, Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx),
      Set.indicator_of_mem (show x + y.1 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun i => add_mem (hx i) (hy.1 i))]
    rfl
  · rw [schr, Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx),
      Set.indicator_of_notMem (show x + y.1 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hx fun i => by
        simpa using sub_mem (h i) (hy.1 i)), mul_zero]

theorem eq_std {ψ : AddChar (AF F) ℂ} (hψ : PsiUnr ψ v) {Φ : (κ → Fv F v) → ℂ} (h : ∀ y ∈ intW v, schr (psiV ψ v) y Φ = Φ) :
    Φ = Φ 0 • Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  classical
  funext x
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have := congrFun (h (x, 0) ⟨hx, fun _ => zero_mem _⟩) 0
    rw [Pi.smul_apply, Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
    simpa [schr] using this
  · rw [Pi.smul_apply, Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), smul_zero]
    obtain ⟨i, hi⟩ := not_forall.1 hx
    obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x i * y) ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hi ((hψ _).1 hc)
    have := congrFun (h (0, Pi.single i y) ⟨fun _ => zero_mem _, fun j => by
      by_cases e : j = i
      · subst e; simpa using hy
      · simp [Pi.single_eq_of_ne e]⟩) x
    simp only [schr, dotProduct_single, zero_dotProduct, mul_zero, add_zero, Pi.zero_apply, zero_mul] at this
    exact (mul_left_eq_self₀.1 this).resolve_left hne

theorem finite_adelic_estimates_holds : FinSt := by
  intro F _ _ ψ hψ κ _ S hS
  classical
  have hsy : ∀ (v : Pl F) y y', ((locE v S).symm y).1 ⬝ᵥ ((locE v S).symm y').2 - ((locE v S).symm y').1 ⬝ᵥ ((locE v S).symm y).2 =
      y.1 ⬝ᵥ y'.2 - y'.1 ⬝ᵥ y.2 := fun v y y' => by
    have := congrArg (evFin F v) (hS (S.symm (liftW v y)) (S.symm (liftW v y')))
    rw [S.apply_symm_apply, S.apply_symm_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sub, map_sum, map_mul, liftW, evFin_liftV] at this
    exact this.symm
  choose ι hb hi using fun v : Pl F => Mod.model ((adjoint_statement.psi F ψ hψ).2 v).1 ((adjoint_statement.psi F ψ hψ).2 v).2 (locE v S).symm (hsy v)
  let s : ∀ v : Pl F, (κ → Fv F v) → ℂ := fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let c : Pl F → ℂ := fun v => if ι v (s v) 0 = 0 then 1 else (ι v (s v) 0)⁻¹
  have hc : ∀ v, c v ≠ 0 := fun v => by
    simp only [c]
    split_ifs with e
    exacts [one_ne_zero, inv_ne_zero e]
  refine ⟨fun v => c v • ι v, fun v => ⟨fun φ hφ => Submodule.smul_mem _ _ ((hb v).1 hφ), fun φ hφ φ' hφ' e =>
    (hb v).2.1 hφ hφ' (smul_right_injective _ (hc v) e), fun Φ hΦ => ?_⟩, fun v w φ hφ => ?_, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := (hb v).2.2 (Submodule.smul_mem _ (c v)⁻¹ hΦ)
    exact ⟨φ, hφ, by rw [LinearMap.smul_apply, e, smul_inv_smul₀ (hc v)]⟩
  · have e : locW v w = (locE v S).symm (locW v (S w)) := by
      change _ = locT v _ _
      rw [locT_locW, LinearEquiv.coe_coe, S.symm_apply_apply]
    rw [LinearMap.smul_apply, LinearMap.smul_apply, e, hi v _ φ hφ]
    funext x
    simp [schr, mul_left_comm]
  · have hd : ∀ᶠ v : Pl F in cofinite, ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal :=
      (Ideal.finite_factors differentIdeal_ne_bot).subset fun v hv => Ideal.dvd_iff_le.2 (not_not.1 hv)
    have h2 : ∀ᶠ v : Pl F in cofinite, evFin F v (algebraMap F (AF F) 2⁻¹) ∈ v.adicCompletionIntegers F :=
      (algebraMap F (AF F) 2⁻¹).2.2
    filter_upwards [hd, h2, locT_int S.symm.toLinearMap] with v e1 e2 e3
    have hu : PsiUnr ψ v := psiUnr_of_not_le hψ v e1
    have e2' : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
      rwa [AlgHom.commutes, map_inv₀, map_ofNat] at e2
    have h := eq_std hu (Φ := ι v (s v)) fun y hy => by
      rw [← hi v y _ (std_mem_SB v)]
      exact congrArg (ι v) (schr_std hu e2' (e3 y hy))
    have h0 : ι v (s v) 0 ≠ 0 := fun e => by
      rw [e, zero_smul] at h
      have := congrFun ((hb v).2.1 (std_mem_SB v) (zero_mem (SB _)) (h.trans (map_zero _).symm)) 0
      rw [Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun i => zero_mem _)] at this
      exact one_ne_zero this
    change c v • ι v (s v) = _
    rw [show c v = (ι v (s v) 0)⁻¹ from if_neg h0, inv_smul_eq_iff₀ h0]
    exact h

end PositivityTheory.Mix
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCGlue
section
noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo
  GlobalTheory.CompanionTheory.Ar.RT.Move

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev stdL (F : Type) [Field F] [NumberField F] (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def Dat (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : Type :=
  {p : SInf F κ × ∀ v : Pl F, (κ → Fv F v) → ℂ // ∀ᶠ v in cofinite, p.2 v = stdL F κ v}

theorem rel_inf (ei : SInf F κ →ₗ[ℂ] SInf F κ) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → SInf F κ)
    (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ) (h : ∑ j ∈ s, c j • pure (f j) (φ j) = 0) :
    ∑ j ∈ s, c j • pure (ei (f j)) (φ j) = 0 := by
  funext x
  have h1 : ∑ j ∈ s, (c j * ∏ᶠ v, φ j v fun i => evFin F v (x i)) • f j = 0 := by
    refine DFunLike.ext _ _ fun y => ?_
    let z : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), (x i).2)
    have := congrFun h z
    have e : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), (x i).2) : AF F)) = y :=
      funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
    rw [sum_apply, zero_apply]
    refine Eq.trans ?_ this
    refine Eq.trans ?_ (Finset.sum_apply z s fun j => c j • pure (f j) (φ j)).symm
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_apply, smul_eq_mul, mul_assoc, mul_comm _ (f j y)]
    exact congrArg (fun z => c j * (f j z * ∏ᶠ v, φ j v fun i => evFin F v (x i))) e.symm
  have h2 := DFunLike.congr_fun (congrArg ei h1) fun i => evI F (x i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, sum_apply, zero_apply] at h2
  rw [Finset.sum_apply, Pi.zero_apply, ← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc,
    mul_comm (ei (f j) _)]

theorem rel_fin (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (hev : ∀ᶠ v in cofinite, ev v (stdL F κ v) = stdL F κ v)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → SInf F κ) (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hφ : ∀ j, ∀ᶠ v in cofinite, φ j v = stdL F κ v) (h : ∑ j ∈ s, c j • pure (f j) (φ j) = 0) :
    ∑ j ∈ s, c j • pure (f j) (fun v => ev v (φ j v)) = 0 := by
  classical
  have key : ∀ T : Finset (Pl F), ∑ j ∈ s, c j • pure (f j) (fun v => if v ∈ T then ev v (φ j v) else φ j v) = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using h
    | insert v T hv ih =>
      have h1 := congrArg (opL v (ev v)) ih
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 : ∀ᶠ w in cofinite, (fun w => if w ∈ T then ev w (φ j w) else φ j w) w = stdL F κ w := by
        filter_upwards [hφ j, T.eventually_cofinite_notMem] with w e1 e2
        simp only [ite_eq_right e2, e1]
      have hop (g : SInf F κ) {θ : ∀ w : Pl F, (κ → Fv F w) → ℂ}
          (hθ : ∀ᶠ w in cofinite, θ w = stdL F κ w) :
          opL v (ev v) (pure g θ) = pure g (Function.update θ v (ev v (θ v))) := by
        let r := pure g (Function.update θ v 1)
        have hr (x : κ → AF F) (y : κ → Fv F v) : r (repl v x y) = r x := by
          unfold r GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
          congr 1
          refine finprod_congr fun w => ?_
          by_cases e : w = v
          · subst w
            simp
          · rw [Function.update_of_ne e]
            congr 1
            funext i
            change evalV F w ((x i).2 - singleFin v _ + singleFin v _) = _
            rw [map_add (f := _), map_sub, evalV_singleFin_ne e, evalV_singleFin_ne e,
              sub_zero, add_zero]
            rfl
        have hu (η : (κ → Fv F v) → ℂ) :
            pure g (Function.update θ v η) = tens (evFin F v) η r := by
          funext x
          have hθ₁ : ∀ᶠ w in cofinite, Function.update θ v 1 w = stdL F κ w := by
            filter_upwards [hθ, eventually_cofinite_ne v] with w hw e
            rw [Function.update_of_ne e, hw]
          have hsupport := finite_mulSupport (vac := stdL F κ)
            (Eventually.of_forall fun _ => rfl) hθ₁ x
          let t (w : Pl F) := if w = v then η (fun i => evFin F v (x i)) else 1
          have ht : (Function.mulSupport t).Finite :=
            (Set.finite_singleton v).subset fun w hw => by
              by_contra e
              exact hw (ite_eq_right e)
          have hprod (w : Pl F) :
              Function.update θ v η w (fun i => evFin F w (x i)) =
                t w * Function.update θ v 1 w (fun i => evFin F w (x i)) := by
            by_cases e : w = v
            · subst w
              simp [t]
            · simp [t, e]
          unfold tens r GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
          rw [funext hprod, finprod_mul_distrib ht hsupport,
            finprod_eq_single t v (fun w e => ite_eq_right e)]
          simp only [t, if_true]
          ac_rfl
        funext x
        have hs : (fun y => pure g θ (repl v x y)) = r x • θ v := by
          have hself := hu (θ v)
          rw [Function.update_eq_self] at hself
          funext y
          rw [hself, tens, piK_repl, hr, Pi.smul_apply, smul_eq_mul, mul_comm]
        change ev v (fun y => pure g θ (repl v x y)) (piK v (finPart x)) = _
        rw [hs, map_smul, hu, tens, Pi.smul_apply, smul_eq_mul, mul_comm]
        rfl
      rw [map_smul, hop _ h2]
      congr 2
      funext w
      rcases eq_or_ne w v with rfl | e
      · simp [hv]
      · simp [e]
  have hfin : {v | ¬ (ev v (stdL F κ v) = stdL F κ v ∧ ∀ j ∈ s, φ j v = stdL F κ v)}.Finite :=
    eventually_cofinite.1 (hev.and ((eventually_all_finset s).2 fun j _ => hφ j))
  rw [← key hfin.toFinset]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  funext v
  split_ifs with e
  · rfl
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at e
    rw [e.2 j hj, e.1]

theorem exists_glue (ei : SInf F κ →ₗ[ℂ] SInf F κ) (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ))
    (hev : ∀ᶠ v in cofinite, ev v (stdL F κ v) = stdL F κ v) : ∃ e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ),
    ∀ f φ, (∀ᶠ v in cofinite, φ v = stdL F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
  let a : (Dat F κ →₀ ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := Finsupp.linearCombination ℂ fun p => pure p.1.1 p.1.2
  let b : (Dat F κ →₀ ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := Finsupp.linearCombination ℂ fun p => pure (ei p.1.1) fun v => ev v (p.1.2 v)
  have hk : LinearMap.ker a ≤ LinearMap.ker b := fun z hz =>
    rel_fin ev hev z.support z (fun p => ei p.1.1) (fun p => p.1.2) (fun p => p.2) (rel_inf ei z.support z _ _ hz)
  obtain ⟨e, he⟩ := ((LinearMap.ker a).liftQ b hk ∘ₗ a.quotKerEquivRange.symm.toLinearMap).exists_extend
  refine ⟨e, fun f φ hφ => ?_⟩
  have h1 : a (Finsupp.single ⟨(f, φ), hφ⟩ 1) = pure f φ := (Finsupp.linearCombination_single ℂ 1 _).trans (one_smul _ _)
  have h2 := LinearMap.congr_fun he ⟨_, LinearMap.mem_range_self a (Finsupp.single ⟨(f, φ), hφ⟩ 1)⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] at h2
  rw [← h1, h2]
  exact (Finsupp.linearCombination_single ℂ 1 _).trans (one_smul _ _)

theorem adelSt_of (hP : PureSt) (hF : FinSt) (hI : InfSt) : AdelSt := by
  intro F _ _ ψ hψ κ _ S hS
  obtain ⟨ev, hb, hi, hs⟩ := hF F ψ hψ κ S hS
  obtain ⟨ei, hei⟩ := hI F κ S hS
  obtain ⟨e, he'⟩ := exists_glue (ei : SInf F κ →L[ℂ] SInf F κ).toLinearMap ev hs
  have he : ∀ f φ, (∀ᶠ v in cofinite, φ v = stdL F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v) := he'
  have hstd : ∀ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, (∀ᶠ v in cofinite, φ v = stdL F κ v) →
      ∀ᶠ v in cofinite, ev v (φ v) = stdL F κ v := fun φ h => by
    filter_upwards [h, hs] with v e1 e2
    rw [e1, e2]
  refine ⟨e, ei, ev, fun Φ hΦ => schA_le ((schA F κ).comap e) (fun f φ h1 h2 => ?_) hΦ, fun w Φ hΦ => ?_, hb,
    fun v w hw φ hφ φ₁ h₁ => ?_, hs, fun f φ _ h => he f φ h⟩
  · rw [Submodule.mem_comap, he f φ h2]
    exact pure_mem_schA _ _ (fun v => (hb v).1 (h1 v)) (hstd φ h2)
  · let L : ∀ u : (κ → AF F) × (κ → AF F), ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := fun u =>
      { toFun := schr ψ u
        map_add' := fun _ _ => funext fun _ => by simp [schr, mul_add]
        map_smul' := fun _ _ => funext fun _ => by simp [schr, mul_left_comm] }
    refine schA_le (LinearMap.eqLocus (e ∘ₗ L w) (L (S w) ∘ₗ e)) (fun f φ h1 h2 => ?_) hΦ
    change e (schr ψ w _) = schr ψ (S w) (e _)
    obtain ⟨⟨g, hg⟩, h⟩ := hP F ψ hψ κ w f
    rw [(h φ h2).2 g hg, he _ _ (h φ h2).1, he f φ h2, ((hP F ψ hψ κ (S w) (ei f)).2 _ (hstd φ h2)).2 _ (hei w f g hg)]
    congr 1
    funext v
    exact hi v w _ (h1 v)
  · have hw' : At (evFin F v) (S w) := fun u hu => by rw [← map_smul, hw u hu, map_zero]
    rw [action_uniqueness F κ v _ φ hφ _ _ h₁ (ad_heis ψ w hw φ), hi v w φ hφ]
    exact ad_heis ψ (S w) hw' (ev v φ)

end PositivityTheory.Mix
end
end

