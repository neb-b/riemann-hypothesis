module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NtExpand
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Fix
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_eq {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    CaseU.cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_mem {w : Plc L} (x : UA L n) (P : Subgroup (GLw n w)) (hx : cLoc w x ∈ P) :
    CaseU.cmp n w ((away l L n).rangeRestrict x) ∈ P := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · rw [cmp_eq h]
    exact hx
  · unfold CaseU.cmp
    rw [dite_eq_right h]
    exact P.one_mem

private theorem st_away (s : HidaSetting l L Ω) (u : s.St) : ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal := fun h => by
  refine s.St_l u.1 u.2 ((s.hA u.1 _).1 ?_)
  have h1 := (s.hw u.1 _).2 h
  simpa using h1

private theorem UpperTheory.V.Hi.inf_one {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n} (hk : k ∈ finU (E := L) (n := n)) :
    infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

private theorem key {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {d m : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (F : Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) {x : UA L n} (hx : x ∈ finU (E := L) (n := n))
    (hl : ∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) (a : Fin m → ℂ) (i : Fin m)
    (h : ∀ g k, ∑ j, a j * F j (g * ((away l L n).rangeRestrict x, 1)) k = F i g k) (ℓ) :
    ∑ j : Fin m, a j • RU L n x (toForm ι e (F j) ℓ) = toForm ι e (F i) ℓ := by
  funext g
  rw [Finset.sum_apply]
  have e1 : ∀ j, RU L n x (toForm ι e (F j) ℓ) g = ℓ (infRep ι lam g⁻¹ (e (F j
      (((away l L n).rangeRestrict g, fun v : V.frame.Vl => cLoc (s.w v.1) g) * ((away l L n).rangeRestrict x, 1))))) := fun j => by
    change toForm ι e (F j) ℓ (g * x) = _
    unfold toForm
    rw [mul_inv_rev, map_mul, UpperTheory.V.Hi.inf_one V ι lam (inv_mem hx), one_mul]
    simp only [map_mul, hl, mul_one, Prod.mk_mul_mk]
  have e2 : ∀ g, F i g = ∑ j, a j • F j (g * ((away l L n).rangeRestrict x, 1)) := fun g => funext fun k => by
    rw [← h g k, Finset.sum_apply]
    rfl
  simp only [Pi.smul_apply, e1]
  unfold toForm
  rw [e2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Hi.partUR2Fix :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ (F : Fin m → (hset Q τ₀).X.Fn ℂ d), F ∈ (hset Q τ₀).Big ι ξ → ∀ x ∈ finU (E := L) (n := n), (∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) → ∀ k : KT n (wt s), (∀ u : s.St, k.1 u = cLoc (s.w u) x) → cLoc (s.w s.v0) x ∈ Kc _ n 1 →
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) → (∀ q, cLoc (Q.wq q) x = 1) →
    ∀ (i : Fin m) ℓ, ∑ j : Fin m, ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) k i j • RU L n x (toForm ι e (F j) ℓ) = toForm ι e (F i) ℓ := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c ι m τ₀ lam d e ξ _ F hF x hx hl k hk h0 hS hQ i ℓ
  let u : Ub n s := ⟨(away l L n).rangeRestrict x, Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u =>
    cmp_mem x _ (hk u ▸ k.2 u trivial), cmp_mem x _ h0⟩⟩
  have hu : u ∈ UQ n Q := Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw =>
    cmp_mem x _ (hS w hw), Subgroup.mem_iInf.2 fun q =>
      Subgroup.mem_bot.1 (cmp_mem (l := l) x ⊥ (Subgroup.mem_bot.2 (hQ q)))⟩
  have hk' : toKT n s u = k := Subtype.ext (funext fun a => (cmp_eq (st_away s a) x).trans (hk a).symm)
  have h1 := hF.2 u hu
  rw [← hk']
  exact key V ι lam e F hx hl _ i (fun g b => congrFun (congrFun (congrFun h1 i) g) b) ℓ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ThetaEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

private theorem th_Uc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (W : Subgroup kˣ) (hW : IsOpen (W : Set kˣ)) : ∃ c, ∀ d, c ≤ d → Uc k d ≤ W := by
  obtain ⟨c, hc⟩ := (glBridge k 1 ℂ 1).2.2.2.1 (W.comap Matrix.GeneralLinearGroup.det)
    (hW.preimage Matrix.GeneralLinearGroup.continuous_det)
  refine ⟨c, fun d hd => ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have h1 : (u : 𝒪[k]) - 1 ∈ maximalIdeal 𝒪[k] ^ c :=
    Ideal.pow_le_pow_right hd (Ideal.Quotient.eq.1 (congrArg Units.val hu))
  have h2 := hc (x := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (diagT 𝒪[k] (Fin 1) fun _ => u))
    ⟨_, by
      ext i j
      rw [Subsingleton.elim j i]
      simpa [val_diagT] using Ideal.Quotient.eq.2 h1, rfl⟩
  convert Subgroup.mem_comap.1 h2 using 1
  ext
  simp [val_diagT]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}

private theorem th_fin (ha : IsLocalArtin h a) {B : Type} [CommGroup B] [Finite B] (f : Weil h →* B)
    (hf : GlobalTheory.WeilDeligne.IsSmooth f) : ∃ c, ∀ d, c ≤ d → ∀ σ, a σ ∈ Uc _ d → f σ = 1 := by
  choose φ hφ using fun b : {b : B // b ≠ 1} => CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity B ℂ b.2
  choose χ hχ e using fun b => ha.factor ((φ b).comp f) (hf.of_le fun σ hσ => by simp [hσ])
  obtain ⟨c, hc⟩ := th_Uc (⨅ b, (χ b).ker) (by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hχ)
  refine ⟨c, fun d hd σ hσ => by_contra fun h1 => hφ ⟨_, h1⟩ ?_⟩
  exact (DFunLike.congr_fun (e ⟨_, h1⟩) σ).trans (Subgroup.mem_iInf.1 (hc d hd hσ) _)

private theorem th_char (ha : IsLocalArtin h a) {R : Type} [CommRing R] [IsCNL R] (ψ : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (maximalIdeal R) fun g => (ψ g : R)) :
    ∃ χ : (w.adicCompletion F)ˣ →* Rˣ, (∀ (x : Weil h) (g : Dec (F := F) A), (g : G F Ω) = x → χ (a x) = ψ g) ∧
      ∀ N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ y : R) - 1 ∈ maximalIdeal R ^ N := by
  let f := ψ.comp (Subgroup.inclusion (Weil_le_Dec h))
  have key : ∀ N, ∃ c, ∀ d, c ≤ d → ∀ σ, a σ ∈ Uc _ d → (f σ : R) - 1 ∈ maximalIdeal R ^ N := fun N => by
    haveI : Finite (R ⧸ maximalIdeal R) := IsCNL.finite
    haveI : Finite (R ⧸ maximalIdeal R ^ N) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    obtain ⟨c, hc⟩ := th_fin ha ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N)).toMonoidHom).comp f) (by
      have := ((hψ N).comp_continuous (f := fun σ : Ine (F := F) A => Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ))
        (continuous_subtype_val.subtype_mk _)) {1}
      exact (congrArg IsOpen (Set.ext fun σ => Units.ext_iff)).mpr this)
    exact ⟨c, fun d hd σ hσ => Ideal.Quotient.eq.1 (congrArg Units.val (hc d hd σ hσ))⟩
  have hk : a.ker ≤ f.ker := fun σ hσ => by
    refine Units.ext (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R).2 fun N => ?_)
    obtain ⟨c, hc⟩ := key N
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact hc c le_rfl σ (by rw [show a σ = 1 from hσ]; exact one_mem _)
  have hf : ∀ x, a.liftOfSurjective ha.surj ⟨f, hk⟩ (a x) = f x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply a _ _ ⟨f, hk⟩ x
  refine ⟨a.liftOfSurjective ha.surj ⟨f, hk⟩, fun x g e => (hf x).trans (congrArg ψ (Subtype.ext e.symm)), fun N => ?_⟩
  obtain ⟨c, hc⟩ := key N
  refine ⟨c, fun d hd y hy => ?_⟩
  obtain ⟨σ, rfl⟩ := ha.surj y
  rw [hf]
  exact hc d hd σ hy

private theorem th_eps {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R] {l : ℕ} [Fact l.Prime]
    (j : ℤ_[l] →+* R) [IsLocalHom j] {e : Γ → ℤ_[l]} (he : Continuous e) :
    Alg.AdicCont (maximalIdeal R) fun g => j (e g) := fun N => by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have ho : IsOpen {y : Γ | ‖e y - e x‖ < (l : ℝ) ^ (-(N : ℤ))} :=
    isOpen_lt (by fun_prop) continuous_const
  have hl : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  filter_upwards [ho.mem_nhds (by simpa using pow_pos hl N)] with y hy
  refine Ideal.Quotient.eq.2 ?_
  have h1 : e y - e x ∈ maximalIdeal ℤ_[l] ^ N := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 hy.le
  rw [← map_sub]
  refine Ideal.pow_right_mono (I := (maximalIdeal ℤ_[l]).map j) ?_ N ?_
  · exact Ideal.map_le_iff_le_comap.2 fun z hz => map_nonunit j z hz
  · rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h1

private theorem th_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (i : ℕ) : Alg.AdicCont I fun x => f x * g x ^ i := fun N => by
  simp only [map_mul, map_pow]
  exact (hf N).mul ((hg N).comp (· ^ i))

private theorem th_diag (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∃ D : (glIwa k n).T →* (Fin n → kˣ), (∀ i y, D (eT k n i y) = Pi.mulSingle i (y : kˣ)) ∧
      ∀ c (t : (glIwa k n).T), (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → ∀ i, D t i ∈ Uc k (c + 1) := by
  have hi : Function.Injective (diagT k (Fin n)) := fun s t e => by
    have := congrArg Units.val e
    rw [val_diagT, val_diagT] at this
    exact funext fun i => Units.ext (congrFun (Matrix.diagonal_injective this) i)
  let D : (glIwa k n).T →* (Fin n → kˣ) :=
    (MonoidHom.ofInjective hi).symm.toMonoidHom.comp (Subgroup.inclusion (glIwa k n).T_le)
  have hD : ∀ t, diagT k (Fin n) (D t) = t := fun t => MonoidHom.apply_ofInjective_symm hi _
  refine ⟨D, fun i y => hi (hD _), fun c t ht i => ?_⟩
  obtain ⟨y, e, hy⟩ := (glBridge k n ℂ 1).2.2.2.2.2.2.2.2.2 t
  have e2 : D t = fun i => (y i : kˣ) := hi <| by
    rw [hD, e]
    show (List.ofFn (diagT k (Fin n) ∘ fun i => Pi.mulSingle i (y i : kˣ))).prod = _
    rw [← List.map_ofFn, ← map_list_prod, List.prod_ofFn, Finset.univ_prod_mulSingle]
  rw [e2]
  exact hy c ht i

private theorem th_char' (ha : IsLocalArtin h a) {R : Type} [CommRing R] [IsCNL R] (ψ ε : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (maximalIdeal R) fun g => (ψ g : R)) (hε : Alg.AdicCont (maximalIdeal R) fun g => (ε g : R)) (i : ℕ) :
    ∃ χ : (w.adicCompletion F)ˣ →* Rˣ,
      (∀ (x : Weil h) (g : Dec (F := F) A), (g : G F Ω) = x → ψ g * ε g ^ i * χ (a x) = 1) ∧
      ∀ N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ y : R) - 1 ∈ maximalIdeal R ^ N := by
  obtain ⟨χ, h1, h2⟩ := th_char ha (ψ * ε ^ i)⁻¹ fun N => by
    refine (congrArg IsLocallyConstant (funext fun g => ?_)).mpr ((th_mul hψ hε i N).comp_continuous continuous_inv)
    refine congrArg (Ideal.Quotient.mk _) ?_
    simp only [MonoidHom.inv_apply, ← map_inv]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
  exact ⟨χ, fun x g e => by rw [h1 x g e]; exact mul_inv_cancel _, h2⟩

private theorem th_torus (n : ℕ) {V : Type} [Fintype V] (S : V → Plc F) {R : Type} [CommRing R] [IsLocalRing R]
    (χ : ∀ v, Fin n → ((S v).adicCompletion F)ˣ →* Rˣ)
    (hc : ∀ v i N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ v i y : R) - 1 ∈ maximalIdeal R ^ N) :
    ∃ θ : (iwS n S).T →* Rˣ, (∀ v i y, θ (eV n S v i y) = χ v i y) ∧ (iwS n S).ContChar θ := by
  classical
  choose D hD hDc using fun v => th_diag ((S v).adicCompletion F) n
  let p : ∀ v, (iwS n S).T →* (glIwa ((S v).adicCompletion F) n).T := fun v =>
    ((Pi.evalMonoidHom (fun v => GLw n (S v)) v).comp (iwS n S).T.subtype).codRestrict _ fun t => t.2 v trivial
  let θ : (iwS n S).T →* Rˣ := ∏ v, ∏ i, (χ v i).comp ((Pi.evalMonoidHom _ i).comp ((D v).comp (p v)))
  have hθ : ∀ t, θ t = ∏ v, ∏ i, χ v i (D v (p v t) i) := fun t => by
    simp only [θ, MonoidHom.finsetProd_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
  refine ⟨θ, fun v i y => ?_, fun N => ?_⟩
  · have e : D v (p v (eV n S v i y)) = Pi.mulSingle i (y : ((S v).adicCompletion F)ˣ) :=
      (congrArg (D v) (Subtype.ext (Pi.mulSingle_eq_same (M := fun v => GLw n (S v)) _ _))).trans (hD v i y)
    rw [hθ, Finset.prod_eq_single v, Finset.prod_eq_single i]
    · rw [e, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [e, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
    · intro v' _ hv
      rw [show p v' (eV n S v i y) = 1 from Subtype.ext (Pi.mulSingle_eq_of_ne (M := fun v => GLw n (S v)) hv _)]
      simp
    · simp
  · choose d hd using fun x : V × Fin n => hc x.1 x.2 N
    refine ⟨Finset.univ.sup d, fun t ht => ?_⟩
    refine Ideal.Quotient.eq.1 ?_
    rw [hθ]
    simp only [Units.coe_prod, map_prod, map_one]
    refine Finset.prod_eq_one fun v _ => Finset.prod_eq_one fun i _ => ?_
    exact Ideal.Quotient.eq.2 (hd (v, i) _ ((Finset.le_sup (Finset.mem_univ _)).trans (Nat.le_succ _)) _
      (hDc v _ (p v t) (ht v trivial) i))

private theorem th_free {Γ Ga Gp A : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) {U : Subgroup X.Ub} (hU : X.Neat U) : X.Free τ θ U := by
  intro g γ u hu b hb e
  obtain ⟨rfl, rfl⟩ := hU g γ u hu b hb e
  refine ⟨one_mem _, one_mem _, ?_⟩
  rw [show (⟨1, one_mem _⟩ : X.I.T) = 1 from rfl, map_one, map_one]
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.Hi.thetaEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ (r : Resid V.frame c.O n) (Λ : LamObj r), ∃ θ : (hset Q τ₀).X.I.T →* Λ.Λˣ, IsTheta Q τ₀ Λ θ ∧ (hset Q τ₀).IsWt θ := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ r Λ
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (abelian₂.dvr_finite l c.O).2.2.2.2.2
  haveI : IsCNL Λ.Λ := IsCNL.ofCO c.O Λ.Λ
  choose ψ hψ hκ using Λ.inert
  have ha : ∀ v : V.frame.Vl, IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := fun v =>
    Classical.epsilon_spec (Loc.localArtinReciprocity H (s.hw v.1))
  choose χ hχ hc using fun (v : V.frame.Vl) (i : Fin n) =>
    th_char' (ha v) (ψ v i) ((hset Q τ₀).epsV Λ.Λ v) (hψ v i).cont
      (th_eps ((algebraMap c.O Λ.Λ).comp (algebraMap ℤ_[l] c.O))
        (e := fun g : Dec (F := L) (s.A v.1) => (cycZ L Ω l g : ℤ_[l]))
        (Units.continuous_val.comp ((continuous_cycZ L Ω l).comp continuous_subtype_val))) i
  obtain ⟨θ, h1, h2⟩ := th_torus n (fun v : V.frame.Vl => s.w v.1) χ hc
  refine ⟨θ, fun v i x g hg y e1 e2 => ?_, h2, fun K => th_free _ _ _ (neatU l L Ω s n hn V Q c m τ₀ K)⟩
  have e3 := hχ v i x g e1
  rw [e2, ← h1] at e3
  rw [hκ]
  exact e3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtOfForm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem cLoc_inf {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {x : UA L n} (h : x ∈ infU L n)
    (u : Plc L) : cLoc u x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := h
  have e : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc L u) (Matrix.GeneralLinearGroup.map (pFin L) x.1) := Units.ext rfl
  rw [e, h1, map_one]

private theorem exists_gen {M : Type} [AddCommGroup M] [Module ℂ M] (B : Submodule ℂ M) (T : Set M)
    (h : B ⊓ Submodule.span ℂ T ≠ ⊥) : ∃ x ∈ T, x ≠ 0 := by
  by_contra hc
  refine h ?_
  rw [Submodule.span_eq_bot.2 fun x hx => by_contra fun h0 => hc ⟨x, hx, h0⟩, inf_bot_eq]

private theorem wt_of_form {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) (V : s.Lev) (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (J : UA L n → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1))
    (hJ : ∀ x, J x = ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x))
    (h3 : ∀ (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) ℓ (x : UA L n),
      RU L n x (toForm ι e F ℓ) = toForm ι e (fun g => F (g * J x)) (ℓ ∘ₗ infRep ι lam x⁻¹))
    (h4 : Function.Surjective (fun k : finU (E := L) (n := n) => J k))
    (σ : Submodule ℂ (UA L n → ℂ)) (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) (hF : F ≠ 0)
    (hσ : ∀ ℓ, toForm ι e F ℓ ∈ σ) (y : Emb l (fun v : V.frame.Vl => s.w v.1)) :
    HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual := by
  haveI : Finite V.frame.Vl := @Finite.of_fintype _ V.frame.finV
  haveI : ∀ v : V.frame.Vl, Finite (W.Emb l (s.w v.1)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _
  let Φ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
    { toFun := fun ℓ => toForm ι e F ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine UpperTheory.hasWeightAt_of_tensor_dual_intertwiner L n hn _ (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => ι.toRingHom.comp y.res)
    (UpperTheory.injective_infinitePlace_of_emb_at_split_places l L Ω s V ι) (fun y => lam y.res) σ Φ (fun h0 => hF (funext fun p => ?_)) hσ (fun ℓ x hx => ?_) y
  · obtain ⟨k, hk⟩ := h4 p
    have h1 : infRep (V := V) ι lam (k : UA L n)⁻¹ (e (F p)) = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => by
        have h2 := congrFun (LinearMap.congr_fun h0 ℓ) (k : UA L n)
        rw [← hk]
        simp only [hJ]
        exact h2
    have h2 := congrArg (infRep (V := V) ι lam (k : UA L n)) h1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_zero] at h2
    exact e.map_eq_zero_iff.1 h2
  · have h1 : J x = 1 := (hJ x).trans
      (Prod.ext (Subtype.ext (funext fun u => cLoc_inf hx u.1)) (funext fun v => cLoc_inf hx _))
    have h2 := h3 F ℓ x
    simp only [h1, mul_one] at h2
    exact h2

theorem UpperTheory.V.Hi.partUR2Wt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ _ hY y
  obtain ⟨F, hF, hF0⟩ := exists_gen _ _ hY
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hF0
  obtain ⟨-, -, h3, h4, -⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl
  exact wt_of_form hn V ι e _ (fun _ => rfl) h3 h4 σ (F i) hi (hF i) y
end

