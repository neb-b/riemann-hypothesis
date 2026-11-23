module

public import GroundTheory.AutomorphicForms.MeasuresGL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CasTrace
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}

private def pw (σ : k ≃+* k) (t : Fin n → kˣ) : ℕ → Fin n → kˣ
  | 0 => 1
  | m + 1 => t * fun i => Units.map (σ : k →* k) (pw σ t m i)

private theorem val_pw {σ : k ≃+* k} (h : Isom σ) (t : Fin n → kˣ) (i : Fin n) :
    ∀ m, valuation k (pw σ t m i : k) = valuation k (t i : k) ^ m
  | 0 => by simp [pw]
  | m + 1 => by
    have := h (pw σ t m i)
    simp only [pw, Pi.mul_apply, Units.val_mul, map_mul, Units.coe_map, MonoidHom.coe_coe, this, val_pw h t i m, pow_succ']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem sg_diag (σ : k ≃+* k) (s : Fin n → kˣ) :
    Loc.sg σ (diagT k (Fin n) s) = diagT k (Fin n) fun i => Units.map (σ : k →* k) (s i) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sg_val, val_diagT, val_diagT, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem small {t : Fin n → kˣ} (ht : Strict t) {r : ValueGroupWithZero k} (hr : r ≠ 0) :
    ∀ᶠ m : ℕ in atTop, ∀ i j, i < j → valuation k (t i : k) ^ m ≤ r * valuation k (t j : k) ^ m := by
  simp only [eventually_all]
  intro i j hij
  have h0 : valuation k (t j : k) ≠ 0 := by simp
  have h1 : valuation k (t i : k) / valuation k (t j : k) < 1 := (div_lt_one₀ (zero_lt_iff.2 h0)).2 (ht i j hij)
  obtain ⟨M, hM⟩ := exists_pow_lt₀ h1 (Units.mk0 r hr)
  filter_upwards [eventually_ge_atTop M] with m hm
  have h2 : (valuation k (t i : k) / valuation k (t j : k)) ^ m ≤ r := (pow_le_pow_right_of_le_one' h1.le hm).trans hM.le
  rwa [div_pow, div_le_iff₀ (zero_lt_iff.2 (pow_ne_zero _ h0))] at h2

private theorem unif {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {e : V →ₗ[ℂ] V} (he : IsAvg π K e) (Z : Submodule ℂ V)
    [FiniteDimensional ℂ Z] (hZ : Z ≤ twKer π (unipB k (Fin n)) 1) {t : Fin n → kˣ} (ht : Strict t) {σ : k ≃+* k} (h : Isom σ) :
    ∃ m, 0 < m ∧ ∀ v ∈ Z, e (π (diagT k (Fin n) (pw σ t m)) v) = 0 := by
  obtain ⟨s, hs⟩ := (Submodule.fg_top Z).1 (Module.finite_def.1 inferInstance)
  have : ∀ᶠ m : ℕ in atTop, ∀ v ∈ s, e (π (diagT k (Fin n) (pw σ t m)) v) = 0 := by
    rw [eventually_all_finset]
    intro v hv
    obtain ⟨r, hr, hk⟩ := kerKill k n V π K hK e he v (hZ (hs ▸ Submodule.subset_span hv))
    filter_upwards [small ht hr] with m hm
    exact hk _ fun i j hij => by rw [val_pw h, val_pw h]; exact hm i j hij
  obtain ⟨m, hm, h0⟩ := (this.and (eventually_gt_atTop 0)).exists
  refine ⟨m, h0, fun v hv => ?_⟩
  have : Z ≤ LinearMap.ker (e ∘ₗ π (diagT k (Fin n) (pw σ t m))) := hs ▸ Submodule.span_le.2 hm
  exact this hv

end SlopeTestRemainingChoices

private theorem trIn_smul' {X : Type} [AddCommGroup X] [Module ℂ X] {P : Submodule ℂ X} {T : X →ₗ[ℂ] X}
    (h : ∀ y ∈ P, T y ∈ P) (c : ℂ) : trIn P (c • T) = c * trIn P T := by
  have h' : ∀ y ∈ P, (c • T) y ∈ P := fun y hy => P.smul_mem c (h y hy)
  rw [trIn, trIn, dite_eq_left h, dite_eq_left h', ← smul_eq_mul, ← map_smul]
  rfl

theorem UpperTheory.Gal.Join.casTrace :
    UpperTheory.Gal.Join.CasTrace := by
  intro k _ _ _ _ n V _ _ π ha _ _ μ _ K hK σ A hA hσ hst t ht
  have hd : Dom t := fun i j h => (ht i j h).le
  obtain ⟨e, he, hc⟩ := avgEx _ V π ha.1 K hK.co
  have hAe : ∀ v, A (e v) = e (A v) := hc (Loc.sg σ) A hA (fun g hg => (hst g).2 hg) fun g hg => by
    have e1 : Loc.sg σ (Loc.sg σ.symm g) = g := Units.ext (Matrix.ext fun i j => σ.apply_symm_apply _)
    exact ⟨Loc.sg σ.symm g, (hst _).1 (by rwa [e1]), e1⟩
  have hfix : ∀ v ∈ fixed π K, A v ∈ fixed π K := fun v hv => by rw [← he.fix v hv, hAe]; exact he.mem _
  haveI : μ.IsMulRightInvariant := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k n μ
  haveI : FiniteDimensional ℂ (fixed π K) := ha.2 K hK.co.2 hK.co.1
  refine ⟨_, dcosOp _ V μ π ha.1 K hK.co e he (diagT k (Fin n) t), ?_⟩
  obtain ⟨-, s1, s2⟩ := imStab k n V π ha K hK
  change HasFinTrace (((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A) _
  have hq : ((Real.sqrt (deltaB t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (deltaB_pos _)).ne'
  have key := traceQuot V _ (fixed π K) (((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A)
    (twKer π (unipB k (Fin n)) 1).mkQ
    (((μ.real (K : Set (GL (Fin n) k)) : ℂ) * ((Real.sqrt (deltaB t) : ℝ) : ℂ)⁻¹) • (jacB π t ∘ₗ jacA hA))
    (fun v => Submodule.smul_mem _ _ (he.mem _)) (fun v hv => ?_) fun v hv h0 => ?_
  · rwa [trIn_smul' (P := (fixed π K).map (twKer π (unipB k (Fin n)) 1).mkQ) (T := jacB π t ∘ₗ jacA hA)
      fun y hy => s1 t _ (s2 σ A hA hst y hy)] at key
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
    rw [he.fix _ (hfix v hv), (heckeMul k n V π K hK e he t hd _ (hfix v hv)).2, jacNorm k n V π, smul_smul,
      (dcosVol k n μ K hK t hd).2]
    congr 1
    have h2 : ((deltaB t : ℝ) : ℂ) = ((Real.sqrt (deltaB t) : ℝ) : ℂ) * ((Real.sqrt (deltaB t) : ℝ) : ℂ) := by
      exact_mod_cast (Real.mul_self_sqrt (deltaB_pos t).le).symm
    push_cast
    rw [h2]
    field_simp
  · obtain ⟨m, -, hm⟩ := unif hK he (fixed π K ⊓ twKer π (unipB k (Fin n)) 1) inf_le_right ht hσ
    have hZ : ∀ j : ℕ, (A ^ j) v ∈ fixed π K ⊓ twKer π (unipB k (Fin n)) 1 := fun j => by
      induction j with
      | zero => exact ⟨hv, (Submodule.Quotient.mk_eq_zero _).1 h0⟩
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply]
        refine ⟨hfix _ ih.1, (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
        rw [← jacA_mk hA, (Submodule.Quotient.mk_eq_zero _).2 ih.2, map_zero]
    have hP : ∀ j : ℕ, ((((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A) ^ j) v =
        (μ.real (dcos K t) : ℂ) ^ j • e (π (diagT k (Fin n) (pw σ t j)) ((A ^ j) v)) := fun j => by
      induction j with
      | zero => simp [pw, he.fix v hv]
      | succ j ih =>
        have hdj : Dom fun i => Units.map (σ : k →* k) (pw σ t j i) := fun a b hab => by
          have h1 := hσ (pw σ t j a)
          have h2 := hσ (pw σ t j b)
          simp only [Units.coe_map, MonoidHom.coe_coe, h1, h2, val_pw hσ]
          exact pow_le_pow_left' (hd a b hab) j
        rw [pow_succ', Module.End.mul_apply, ih, map_smul]
        simp only [LinearMap.comp_apply, LinearMap.smul_apply]
        rw [hAe, he.fix _ (he.mem _), hA, sg_diag, (heckeMul k n V π K hK e he _ hdj _ (hfix _ (hZ j).1)).1 t hd, smul_smul,
          ← pow_succ, pow_succ' A]
        rfl
    exact ⟨m, by rw [hP, hm _ (hZ m), smul_zero]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TorusCharComp
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join

private theorem trIn_smul {X : Type} [AddCommGroup X] [Module ℂ X] {P : Submodule ℂ X} {T : X →ₗ[ℂ] X}
    (h : ∀ y ∈ P, T y ∈ P) (c : ℂ) : trIn P (T ∘ₗ (c • LinearMap.id)) = c * trIn P T := by
  have h' : ∀ y ∈ P, (T ∘ₗ (c • LinearMap.id)) y ∈ P := fun y hy => h _ (P.smul_mem c hy)
  rw [trIn, trIn, dite_eq_left h, dite_eq_left h', ← smul_eq_mul, ← map_smul]
  congr 1
  ext y
  simp [LinearMap.restrict_apply]

private theorem adm {K : Type} [Field K] [NumberField K] {n : ℕ} {w : Pl K} (τ : SmIrr (Gw n w)) : IsAdmissible τ.ρ :=
  PositivityTheory.Exh.irreducibleAdmissibleGL _ n τ.V τ.ρ τ.smooth τ.irred

theorem liftExp (h : CoreId) : LiftExp := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' μ ⟨y, hy0, hy⟩
  obtain ⟨A, hA, hA0, hc⟩ := h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ'
  obtain ⟨U, hU, hy'⟩ := expLev _ n _ τ.ρ τ.smooth y
  obtain ⟨K', -, K, hK, l', l, hst, c, t₀, hc0, hid⟩ := hc ⊤ U (by simp) hU
  obtain ⟨f', st', sa'⟩ := imStab _ n _ τ'.ρ (adm τ') K' l'
  obtain ⟨f, st, -⟩ := imStab _ n _ τ.ρ (adm τ) K l
  obtain ⟨E', e', m'⟩ := traceExp _ _ (jacB τ'.ρ) (imK τ'.ρ K') st'
  obtain ⟨E₀, e, m⟩ := traceExp _ _ (jacB τ.ρ) (imK τ.ρ K) st
  have hμ : μ.comp (nT n N) ∈ E₀.map fun μ => μ.comp (nT n N) :=
    Multiset.mem_map_of_mem _ ((m μ).2 ⟨y, hy' K hK, hy0, hy⟩)
  have hid' : ∀ t, Dom t → trIn (imK τ'.ρ K') (jacB τ'.ρ (t₀ * t) ∘ₗ jacA hA) =
      c * ((E₀.map fun μ => μ.comp (nT n N)).map fun μ => (μ (t₀ * t) : ℂ)).sum := fun t ht => by
    rw [hid t ht, e, Multiset.map_map]
    rfl
  obtain ⟨t₁, ht₁, hne⟩ := (charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) _ 1 1 one_ne_zero fun _ _ => rfl).2
    (fun h0 => by rw [h0] at hμ; exact Multiset.notMem_zero _ hμ)
  obtain ⟨μ', hinv, z, -, hz0, hz⟩ := twExp _ _ (jacB τ'.ρ) (imK τ'.ρ K')
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv σw.toMulEquiv) (jacA hA) st' (sa' σw A hA hst)
    (fun t y => jacSemi _ n σw hN.cyc.isom _ τ'.ρ A hA t y) (t₀ * t₁) (by rw [hid' t₁ ht₁]; exact mul_ne_zero hc0 hne)
  obtain ⟨ω', rfl, s', q'⟩ := expSub _ n _ τ'.ρ τ'.smooth τ'.irred μ' ⟨z, hz0, hz⟩
  have i' : ∀ i, Inv σw (ω' i) := fun i x => by
    have h1 := hinv (Pi.mulSingle i x)
    have h2 : ∀ x, torusChar ω' (Pi.mulSingle i x) = ω' i x := fun x => by
      rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp),
        Pi.mulSingle_eq_same]
    rw [← h2, ← h2, ← h1]
    congr 1
    funext j
    change _ = Units.mapEquiv σw.toMulEquiv ((Pi.mulSingle i x : Fin n → _) j)
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      rfl
    · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]
  obtain ⟨-, -, -, c', hc', hsc, -⟩ := locDesc_holds _ n σw _ hN.cyc _ τ'.ρ τ'.irred ω' s' i' q' A hA hA0
  have key := (charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) E' c c' hc0 fun t ht => by
    rw [← hid' t ht, hsc, trIn_smul (st' _), e']).1 _ hμ
  obtain ⟨x, -, hx0, hx⟩ := (m' _).1 key
  exact ⟨x, hx0, hx⟩

private theorem exp_of_sub {K : Type} [Field K] [NumberField K] {n : ℕ} {w : Pl K} (τ : SmIrr (Gw n w))
    {ω : Fin n → (w.adicCompletion K)ˣ →* ℂˣ} (s : ∀ i, IsSmoothChar (ω i)) (q : IsSubquotient τ.ρ (prinSeries ω)) :
    ∃ p : Equiv.Perm (Fin n), IsExp τ.ρ (torusChar (ω ∘ p)) := by
  have hnt : Nontrivial τ.V := GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible τ.irred
  obtain ⟨h1, h2, h3, -⟩ := locDesc_holds _ n (RingEquiv.refl _) 1 ⟨fun _ => rfl, one_pos, fun _ => rfl⟩ _ τ.ρ τ.irred ω s
    (fun _ _ => rfl) q LinearMap.id (fun _ _ => rfl) (fun h => by
      obtain ⟨x, hx⟩ := exists_ne (0 : τ.V)
      exact hx (LinearMap.congr_fun h x))
  obtain ⟨E₀, e, m⟩ := traceExp _ _ (jacB τ.ρ) ⊤ fun _ _ _ => trivial
  have hne : E₀ ≠ 0 := by
    rintro rfl
    have h4 := e 1
    rw [map_one, trIn, dite_eq_left fun _ _ => Submodule.mem_top] at h4
    have h5 : LinearMap.trace ℂ (⊤ : Submodule ℂ (Jacquet τ.ρ (unipB _ (Fin n)))) 1 = 0 := h4
    rw [LinearMap.trace_one, finrank_top, Nat.cast_eq_zero] at h5
    exact Module.finrank_pos.ne' h5
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨y, -, hy⟩ := (m μ).1 hμ
  obtain ⟨p, rfl⟩ := h3 μ ((subQuot _ _ (jacB τ.ρ) μ).1.1 ⟨y, hy⟩)
  exact ⟨p, y, hy⟩

private theorem torusChar_inj {R : Type} [CommRing R] {n : ℕ} {a b : Fin n → Rˣ →* ℂˣ} (h : torusChar a = torusChar b) : a = b := by
  have h2 : ∀ (a : Fin n → Rˣ →* ℂˣ) i x, torusChar a (Pi.mulSingle i x) = a i x := fun a i x => by
    rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp),
      Pi.mulSingle_eq_same]
  funext i
  ext1 x
  rw [← h2, ← h2, h]

private theorem torusChar_comp {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (a : Fin n → Rˣ →* ℂˣ) (N : Sˣ →* Rˣ) :
    (torusChar a).comp (nT n N) = torusChar fun i => (a i).comp N := by
  refine MonoidHom.ext fun t => ?_
  rw [MonoidHom.comp_apply, torusChar_apply, torusChar_apply]
  rfl

theorem liftGood (h : CoreId) : LiftGood := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' ω s q
  obtain ⟨p, hp'⟩ := exp_of_sub τ s q
  have h1 := liftExp h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' _ hp'
  obtain ⟨ω', e, s', q'⟩ := expSub _ n _ τ'.ρ τ'.smooth τ'.irred _ h1
  rw [torusChar_comp] at e
  obtain rfl := torusChar_inj e
  have h2 := subPerm _ n _ τ'.ρ τ'.irred _ s' p.symm q'
  have h3 : (fun i => ((ω ∘ p) i).comp N) ∘ p.symm = fun i => (ω i).comp N := funext fun i => by simp
  rwa [h3] at h2

end UpperTheory.Gal.Join
end

