module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.CharPolSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJacqOfU

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Hi
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.RR.ordAway_of_alt (hX : ExRS) (hGd : GdOf) :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.OrdAway := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H A hA
  have P := PH.toClassicalTheorems
  obtain ⟨p1, p2, p3, p4⟩ := UpperTheory.V.Base.places F Ω l A
  have triv : (∀ g ∈ Ine (F := F) A, r g = 1) → Ine (F := F) A ≤ ξ.ker → IsDiagOn r (Ine (F := F) A) ![1, ξ] :=
    fun h1 h2 => ⟨1, fun g hg => by
      have h3 : ξ g = 1 := h2 hg
      rw [h1 g hg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h3]⟩
  by_cases hT : A = ⊤
  · rw [(p2 hT).1] at triv ⊢
    exact triv (fun g hg => by rw [Subgroup.mem_bot.1 hg, map_one]) bot_le
  obtain ⟨w, h⟩ := p1 hT
  have hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := fun e => hA ((p3 w h).2 e)
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := hX F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F 2 π w
  have mod_retr {R S M : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M]
      [IsSimpleModule R S] (h : ⨆ f : S →ₗ[R] M, LinearMap.range f = ⊤) (x : M) (hx : x ≠ 0) :
      ∃ T : M →ₗ[R] S, T x ≠ 0 := by
    have htop : isotypicComponent R M S = ⊤ := top_le_iff.1 (h ▸ iSup_le fun f => by
      rcases f.injective_or_eq_zero with hi | rfl
      · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
      · simp)
    have : IsSemisimpleModule R M :=
      IsSemisimpleModule.congr (M := isotypicComponent R M S) (LinearEquiv.ofTop _ htop).symm
    have hiso := IsIsotypicOfType.of_isotypicComponent_eq_top htop
    obtain ⟨m, hm, hxm⟩ : ∃ m : Submodule R M, IsCoatom m ∧ x ∉ m := by
      by_contra hn
      push Not at hn
      refine hx ((Submodule.mem_bot R).1 ?_)
      rw [← IsSemisimpleModule.jacobson_eq_bot R M]
      exact Submodule.mem_sInf.2 hn
    obtain ⟨W, hc⟩ := exists_isCompl m
    have : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hc.isCoatom_iff_isAtom.1 hm)
    obtain ⟨e⟩ := hiso W
    refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hc.symm, fun h0 => hxm ?_⟩
    simpa using h0
  have rep_retr {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
      (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
      ∃ T : V →ₗ[ℂ] X, (∀ g v, T (τ g v) = σ g (T v)) ∧ T x ≠ 0 := by
    have key := mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by
        refine top_le_iff.1 fun y _ => ?_
        have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V) := trivial
        rw [← h] at hy
        rw [← τ.asModuleEquiv.symm_apply_apply y]
        refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
        · rintro f _ ⟨v, rfl⟩
          exact Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ
            ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩
        · simp
        · intro a b ha hb
          rw [map_add (f := _)]
          exact add_mem ha hb)
    obtain ⟨T, h2⟩ := key x hx
    let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T
    exact ⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
    have iwahori_level_zero_eq : K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
      ext g
      constructor
      · rintro ⟨k, -, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        refine ⟨k, ?_, rfl⟩
        have : Subsingleton
            (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
          Ideal.Quotient.subsingleton_iff.2 (by simp)
        exact Subsingleton.elim (α := Fin 2 → _) _ _
    obtain ⟨B, hB⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results P F 2 w σ).1
      ⟨T v, hTv, fun u hu => by rw [← hT, hf u (iwahori_level_zero_eq ▸ hu)]⟩
    have hB' : π.HasSat w B := ((_root_.UpperTheory.V.Af.satake_local_of_printed_results P F 2 w σ).2 _ π.finPart (hiso σ hσ) B).2 hB
    exact triv (hG.frob w hl B hB' A h).1
      ((H.ram w A h).2 (Or.inl hc))
  obtain ⟨lam, ⟨v, hv, hf, hU⟩, hlam⟩ := H.away w hc hl
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  have map_dc {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V) (T : V →ₗ[ℂ] X)
      (hT : ∀ g v, T (τ g v) = σ g (T v)) {x : V} (hx : T x ≠ 0) (K : Subgroup Γ) (a : Γ) :
      T (Hi.dc τ K K a x) = Hi.dc σ K K a (T x) := by
    let Q := MulAction.orbit K (a : Γ ⧸ K)
    rcases finite_or_infinite Q with hfinite | hinfinite
    · let _ := Fintype.ofFinite Q
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]
    · have sum_eq_zero {W : Type} [AddCommGroup W] [Module ℂ W]
          (ρ : Representation ℂ Γ W) (y : W) (hy : y ≠ 0) :
          (∑ᶠ q : Q, ρ (q : Γ ⧸ K).out) = 0 := by
        apply finsum_of_infinite_support
        rw [Function.support_eq_univ]
        · exact Set.infinite_univ
        · intro q hρ
          let g := (q : Γ ⧸ K).out
          have hgy : ρ g⁻¹ (ρ g y) = y := by
            rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
          exact hy (by rw [← hgy, show ρ g = 0 from hρ, LinearMap.zero_apply, map_zero])
      have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero])
      rw [Hi.dc, Hi.dc, sum_eq_zero τ x hx0, sum_eq_zero σ (T x) hx]
      simp
  obtain ⟨μ₁, μ₂, L, hL, hμ, -, hlaw⟩ := _root_.UpperTheory.V.Sd.jacqOfU_alt P F w σ (c w) (Units.mk0 lam hl0) hc
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hU, map_smul, Units.val_mk0]⟩
  have exists_ps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : GlobalTheory.PRep.IsSmooth π)
      (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
      (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
        ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
      ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
        ∀ x : kˣ, valuation k (x : k) = 1 → ψ 0 x = μ₁ x := by
    set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
    let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
    have hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
      have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
      have := H 1 1 (u.1.val 0 1) v
      rw [← e] at this
      simp [this]
    let l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hU
    obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hL (LinearMap.ext hn)
    have hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x := fun t x => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]
      rw [UnramFixed.jacB_apply, jacBU_mk, map_smul, e]
      change _ * L _ = _ * L y
      rw [H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]
      simp [χ, torusChar_apply, hδ]
    have hs : IsSmoothChar χ := by
      refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
        ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)
      intro g hg
      have hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := hg
      have h := hle g (Submodule.Quotient.mk v)
      rw [hg'] at h
      exact Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))
    have htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ :=
      MonoidHom.ext fun t => by
        rw [torusChar_apply]
        conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
        rfl
    refine ⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x hx => ?_⟩
    · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
        (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
      rw [← htc] at key
      exact key
    · have h1 : δ (Pi.mulSingle 0 x) = 1 := UnramFixed.deltaHalf_torusO k (t := (Pi.mulSingle 0 x : Fin 2 → kˣ)) fun j => by
        fin_cases j <;> simp [hx]
      change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
      rw [h1]
      simp [torusChar_apply]
  obtain ⟨ψ, hψ, hs, hψ0⟩ := exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨rc, hrc⟩ := recTExists F Ω A w h
  have hpl := (Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
  have hx := (((hG.loc w σ hσ hpl).1 A h rc hrc).1 hl).isWDOf (hGd F Ω A w h rc hrc 2 σ hpl)
  have off_diag {K : Type} [Field K] {Y : Matrix (Fin 2) (Fin 2) K} {x : K} (hx : x ≠ 1)
      (h : Matrix.diagonal ![1, x] * Y = Y * Matrix.diagonal ![1, x]) : Y 0 1 = 0 ∧ Y 1 0 = 0 := by
    have h1 := congrFun (congrFun h 0) 1
    have h2 := congrFun (congrFun h 1) 0
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
    have hx' : x - 1 ≠ 0 := sub_ne_zero.2 hx
    exact ⟨(mul_eq_zero.1 (by linear_combination -h1)).resolve_left hx',
      (mul_eq_zero.1 (by linear_combination h2)).resolve_left hx'⟩
  have nil_zero {K : Type} [Field K] {N : Matrix (Fin 2) (Fin 2) K} {x : K} (hx : x ≠ 1) (hN : IsNilpotent N)
      (h : Matrix.diagonal ![1, x] * N = N * Matrix.diagonal ![1, x]) : N = 0 := by
    obtain ⟨h1, h2⟩ := off_diag hx h
    have e : N = Matrix.diagonal fun i => N i i := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2]
    obtain ⟨k, hk⟩ := hN
    rw [e, Matrix.diagonal_pow] at hk
    rw [e]
    ext i j
    by_cases hij : i = j
    · subst hij
      have := congrFun (congrFun hk i) i
      simp at this
      simp [this.1]
    · simp [hij]
  have unip_one {K : Type} [Field K] [CharZero K] {M : Matrix (Fin 2) (Fin 2) K} (ht : M.trace = 1 + 1) (hd : M.det = 1) {d : ℕ}
      (h0 : 0 < d) (h : M ^ d = 1) : M = 1 := by
    have h2 : (M - 1) * (M - 1) = 0 := by
      rw [Matrix.trace_fin_two] at ht
      rw [Matrix.det_fin_two] at hd
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination M 0 0 * ht - hd
      · linear_combination M 0 1 * ht
      · linear_combination M 1 0 * ht
      · linear_combination M 1 1 * ht - hd
    have h3 : ∀ n : ℕ, M ^ n = 1 + (n : K) • (M - 1) := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        have : (M - 1) * M = M - 1 := by
          rw [← sub_eq_zero, ← h2, mul_sub (M - 1), mul_one]
        rw [pow_succ, ih, add_mul, smul_mul_assoc, this, Nat.cast_succ, add_smul, one_mul, one_smul]
        abel
    rw [h3, add_eq_left, smul_eq_zero, sub_eq_zero] at h
    exact h.resolve_left (Nat.cast_ne_zero.2 h0.ne')
  have diag_all {K : Type} [Field K] [CharZero K] {H : Type} [Group H] (r : H →* GL (Fin 2) K) (ξ : H →* Kˣ)
      (ht : ∀ s, (r s).val.trace = 1 + ξ s) (hd : ∀ s, (r s).val.det = ξ s) (hf : ∀ s, ∃ d, 0 < d ∧ r s ^ d = 1)
      {s₀ : H} (h0 : (ξ s₀ : K) ≠ 1) (e0 : (r s₀).val = Matrix.diagonal ![1, (ξ s₀ : K)]) (s : H) :
      (r s).val = Matrix.diagonal ![1, (ξ s : K)] := by
    have hc : ξ (s₀ * s * (s * s₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (ξ s₀), mul_inv_cancel]
    obtain ⟨d, hd0, h⟩ := hf (s₀ * s * (s * s₀)⁻¹)
    have h1 : r (s₀ * s * (s * s₀)⁻¹) = 1 := Units.ext (unip_one (by rw [ht, hc, Units.val_one]) (by rw [hd, hc, Units.val_one]) hd0
      (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]))
    rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h1
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, Units.val_mul, e0] at h2
    obtain ⟨h3, h4⟩ := off_diag h0 h2
    have t1 := ht s
    have t2 := ht (s₀ * s)
    rw [map_mul, Units.val_mul, e0, map_mul, Units.val_mul] at t2
    rw [Matrix.trace_fin_two] at t1 t2
    simp only [Matrix.diagonal_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at t2
    have h5 : (r s).val 1 1 = ξ s := by
      refine sub_eq_zero.1 ((mul_eq_zero.1 (?_ : ((ξ s₀ : K) - 1) * _ = 0)).resolve_left (sub_ne_zero.2 h0))
      linear_combination t2 - t1
    have h6 : (r s).val 0 0 = 1 := by linear_combination t1 - h5
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h3, h4, h5, h6]
  have diag_of_wd (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin 2) (Qbar l))
      (ξ : G F Ω →* (Qbar l)ˣ) {x : WD h} (hx : IsWDOf ι r x)
      (hc : ∀ g : Ine (F := F) A, ∃ y : ℂ, x.charPol (ineIncl h g) = (X - C 1) * (X - C y))
      (hd : ∀ g ∈ Ine (F := F) A, (r g).val.det = ξ g) (hr : ¬ Ine (F := F) A ≤ ξ.ker) :
      IsDiagOn r (Ine (F := F) A) ![1, ξ] := by
    have ht : ∀ g ∈ Ine (F := F) A, (r g).val.trace = 1 + ξ g := fun g hg => by
      obtain ⟨y, hy⟩ := hc ⟨g, hg⟩
      have e := hx.wdOf_eq hl
      obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
      rw [← e, hN.charPol_wdOf hl ht ι, coe_ineIncl] at hy
      have h1 := congrArg (Polynomial.eval 1) hy
      rw [Matrix.charpoly_fin_two, hd g hg] at h1
      apply ι.injective
      simp at h1
      simp only [map_add (f := _), map_one]
      linear_combination -h1
    obtain ⟨s₀, hs₀, h0⟩ := IsConcreteLE.not_le_iff_exists.1 hr
    have h0' : (ξ s₀ : Qbar l) ≠ 1 := fun e => h0 (Units.ext e)
    obtain ⟨p, hp⟩ := UpperTheory.Reformulated.B.IntertwinerDiagonalization.exists_diag (r s₀) h0' (ht _ hs₀) (hd _ hs₀)
    let r' : G F Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj p).toMonoidHom.comp r
    have hr' : ∀ s, r' s = p * r s * p⁻¹ := fun s => rfl
    obtain ⟨t, htt, φ, hφ, N, a, hN, -⟩ : IsWDOf ι r' x := hx.of_conj hl p fun s => by rw [hr', inv_mul_cancel_right]
    obtain rfl : N = 0 := nil_zero h0' hN.1 (by
      have := hN.comm hl htt (ineIncl h ⟨s₀, hs₀⟩)
      rwa [deg_ineIncl, zpow_zero, one_smul, coe_ineIncl, hr', hp] at this)
    obtain ⟨-, U, hU, H⟩ := hN
    have := compactSpace_Ine (E := F) A
    have : Finite (Ine (F := F) A ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hU
    refine ⟨p, fun s hs => ?_⟩
    refine (diag_all (r'.comp (Ine (F := F) A).subtype) (ξ.comp (Ine (F := F) A).subtype) (fun g => ?_) (fun g => ?_)
      (fun g => ?_) (s₀ := ⟨s₀, hs₀⟩) h0' hp ⟨s, hs⟩).trans ?_
    · exact (Matrix.trace_units_conj p _).trans (ht g g.2)
    · exact (Matrix.det_units_conj p _).trans (hd g g.2)
    · obtain ⟨d, hd, -, hg⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := U)) g
      refine ⟨d, hd, ?_⟩
      rw [← map_pow]
      exact Units.ext (by simpa using H _ hg)
    · congr 1
      ext i
      fin_cases i <;> rfl
  refine diag_of_wd hl ι r ξ hx (fun g => ?_) (fun g hg => ?_)
    fun e => ((H.ram w A h).1 e).elim hc hl
  · obtain ⟨b, hb, ε, hL⟩ := toV' hrc
    obtain ⟨e1, e2⟩ := RR.ps_cls hL σ ψ hψ hs
    have charPol_lpTw (x : WD h) (s : ℝ) (g : Ine (F := F) A) :
        (x.lpTw s).charPol (ineIncl h g) = x.charPol (ineIncl h g) := by
      obtain ⟨n, a, rfl⟩ := x.exists_rep
      rw [WD.lpTw_mk, WD.charPol_mk, WD.charPol_mk]
      congr 1
      ext v
      simp
    rw [e1, charPol_lpTw]
    have h1 := e2 (ineIncl h g)
    have h2 : valuation (w.adicCompletion F) (b (ineIncl h g) : w.adicCompletion F) = 1 :=
      ord_eq_zero_iff.1 (by rw [hb.ord_eq, deg_ineIncl, neg_zero])
    have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [Fin.prod_univ_two, hψ0 _ h2, hμ _ ((isEquiv (valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1 h2)] at h1
    exact ⟨_, h1⟩
  · have h1 := DFunLike.congr_fun H.det g
    have h2 : cycZ F Ω l g = 1 := p4 hA hg
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.zpow_apply, cycBar, h2, map_one, one_zpow,
      one_mul] at h1
    exact congrArg Units.val h1
end
