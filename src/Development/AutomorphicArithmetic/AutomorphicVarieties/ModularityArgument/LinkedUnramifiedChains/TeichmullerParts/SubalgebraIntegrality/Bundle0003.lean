module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0058
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.IndepS
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open GlobalTheory.BCT.GlobLev GlobalTheory.SplitPts GroundTheory.Automorphic

namespace UpperTheory.V.Z.J.D

private theorem exists_avg {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (R : Representation ℂ G V)
    (K H : Subgroup G) (hfin : Finite (K ⧸ H.subgroupOf K)) :
    ∃ A : V →ₗ[ℂ] V, (∀ v, (∀ k ∈ K, R k v = v) → A v = v) ∧
      (∀ v, (∀ h ∈ H, R h v = v) → ∀ k ∈ K, R k (A v) = A v) ∧
      ∀ M : Submodule ℂ V, (∀ x, ∀ v ∈ M, R x v ∈ M) → ∀ v ∈ M, A v ∈ M := by
  classical
  letI := Fintype.ofFinite (K ⧸ H.subgroupOf K)
  have hc : (Fintype.card (K ⧸ H.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card (K ⧸ H.subgroupOf K) : ℂ)⁻¹ • ∑ q : K ⧸ H.subgroupOf K, R ((q.out : K) : G), ?_, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => hv _ (q.out : K).2]
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]
  · intro v hv k hk
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    congr 1
    have key : ∀ q : K ⧸ H.subgroupOf K, R k (R ((q.out : K) : G) v) =
        R ((((⟨k, hk⟩ : K) • q).out : K) : G) v := fun q => by
      have e : (QuotientGroup.mk (((⟨k, hk⟩ : K) • q).out) : K ⧸ H.subgroupOf K) =
          QuotientGroup.mk ((⟨k, hk⟩ : K) * q.out) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h1 := QuotientGroup.eq.1 e
      have h2 : ((((⟨k, hk⟩ : K) • q).out : K) : G)⁻¹ * (k * ((q.out : K) : G)) ∈ H := h1
      have h3 := hv _ h2
      have h4 : k * ((q.out : K) : G) = ((((⟨k, hk⟩ : K) • q).out : K) : G) *
          (((((⟨k, hk⟩ : K) • q).out : K) : G)⁻¹ * (k * ((q.out : K) : G))) := by group
      rw [← Module.End.mul_apply, ← map_mul, h4, map_mul, Module.End.mul_apply, h3]
    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Equiv.sum_comp (MulAction.toPerm (⟨k, hk⟩ : K)) fun q : K ⧸ H.subgroupOf K => R ((q.out : K) : G) v
  · intro M hM v hv
    exact M.smul_mem _ (by
      simp only [LinearMap.sum_apply]
      exact M.sum_mem fun q _ => hM _ v hv)

private theorem is_compact_integral_level {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) :
    IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
  have hO : IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
    rw [globLev_KL_eq hS]
    exact (AdelicGLn.isOpen_integralFiniteGL E n).preimage continuous_finPart
  refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
    ((AdelicGLn.isCompact_integralFiniteGL E n).image continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E n x, ?_, ?_⟩
  · rw [globLev_KL_eq hS] at hx
    exact hx
  · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

private theorem finite_quot {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Set (Pl E)} (hS : IsSection S)
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (hle : ∀ w, K' w ≤ KL n w) (U : Subgroup (finU (E := E) (n := n))) (hU : IsOpen (U : Set (finU (E := E) (n := n)))) :
    Finite (globLev S K' ⧸ U.subgroupOf (globLev S K')) := by
  have hK : globLev S K' ≤ globLev S (KL n) := fun k hk =>
    (mem_globLev S _ k).2 fun w hw => hle w ((mem_globLev S _ k).1 hk w hw)
  haveI : CompactSpace (globLev S (KL n)) := isCompact_iff_compactSpace.1 (is_compact_integral_level hS)
  have h0 : Finite (globLev S (KL n) ⧸ U.subgroupOf (globLev S (KL n))) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have h1 : U.relIndex (globLev S (KL n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : U.relIndex (globLev S K') ≠ 0 := mt (Subgroup.relIndex_eq_zero_of_le_right hK) h1
  haveI : (U.subgroupOf (globLev S K')).FiniteIndex := ⟨h2⟩
  exact Subgroup.finite_quotient_of_finiteIndex

private noncomputable def stabG {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (R : Representation ℂ G V) (v : V) : Subgroup G :=
  _root_.UpperTheory.Reformulated.B.StabilizerSubgroup.stabG R v

theorem indepS : IndepS := by
  intro E _ _ _ n S hS lam K' hK' J _ σ hd
  classical
  obtain ⟨h1, h2, -⟩ := hd
  have hst : ∀ j x, ∀ φ ∈ σ j, RU E n x φ ∈ σ j := fun j => (h1 j).1.stable
  intro i
  have hT : ∀ x, ∀ φ ∈ ⨆ (j) (_ : j ≠ i), σ j, RU E n x φ ∈ ⨆ (j) (_ : j ≠ i), σ j := by
    intro x φ hφ
    have hc : (⨆ (j) (_ : j ≠ i), σ j) ≤ (⨆ (j) (_ : j ≠ i), σ j).comap (RU E n x) :=
      iSup₂_le fun j hj y hy => Submodule.mem_comap.2 (le_iSup₂_of_le (f := fun j (_ : j ≠ i) => σ j) j hj le_rfl (hst j x y hy))
    exact hc hφ
  rcases (h1 i).1.irred (σ i ⊓ ⨆ (j) (_ : j ≠ i), σ j) inf_le_left
    (fun x φ hφ => ⟨hst i x φ hφ.1, hT x φ hφ.2⟩) with h0 | h0
  · exact disjoint_iff.2 h0
  exfalso
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 (h1 i).2.2
  have hφT : φ ∈ ⨆ (j) (_ : j ≠ i), σ j := (inf_eq_left.1 h0) hφ.1
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hφT
  have hfσ : ∀ j, f j ∈ σ j := fun j => by
    by_cases hj : j = i
    · have := hf j
      rw [iSup_neg (not_not.2 hj)] at this
      rw [(Submodule.mem_bot ℂ).1 this]
      exact Submodule.zero_mem _
    · have := hf j
      rwa [iSup_pos hj] at this
  have hfi : f i = 0 := by
    have := hf i
    rw [iSup_neg (not_not.2 rfl)] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hsum' : ∑ j, f j = φ := by
    rw [← hsum]
    exact (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => Finsupp.notMem_support_iff.1 hj).symm
  have hopen : IsOpen ((⨅ j, stabG (RF E n) (f j) : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n))) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j => ((h1 j).1.aut _ (hfσ j)).level
  obtain ⟨A, hA1, hA2, hA3⟩ := exists_avg (RF E n) (globLev S K') (⨅ j, stabG (RF E n) (f j))
    (finite_quot hS (fun w => (hK'.1 w).2.1) _ hopen)
  have hφfix : ∀ k ∈ globLev S K', RF E n k φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ.2 k hk
  have hφA : A φ = φ := hA1 φ hφfix
  have ha : ∀ j, A (f j) ∈ σ j ⊓ fixed (RF E n) (globLev S K') := fun j =>
    ⟨hA3 (σ j) (fun x v hv => hst j _ v hv) _ (hfσ j),
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => hA2 _ (fun h hh => (Subgroup.mem_iInf.1 hh j)) k hk⟩
  have hmem : φ ∈ ⨆ (j) (_ : j ≠ i), σ j ⊓ fixed (RF E n) (globLev S K') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hφA, ← hsum', map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j = i
    · rw [hj, hfi, map_zero]
      exact Submodule.zero_mem _
    · exact le_iSup₂_of_le (f := fun j (_ : j ≠ i) => σ j ⊓ fixed (RF E n) (globLev S K')) j hj le_rfl (ha j)
  exact hφ0 ((Submodule.disjoint_def.1 (h2 i)) φ hφ hmem)

end UpperTheory.V.Z.J.D
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.NormCardLt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z.J.D

namespace UpperTheory.V.Z.J.D

section Emb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {l : ℕ} [Fact l.Prime]

private theorem norm_unif_lt (j : k →+* Qbar l) (hj : Continuous j) : ‖j (unif k : k)‖ < 1 := by
  have hv : Tendsto (fun n : ℕ => ((unif k : kˣ) : k) ^ n) atTop (nhds 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := exists_pow_lt₀ (ValuativeRel.uniformizer_lt_one (R := k)) γ
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Set.mem_setOf_eq, map_pow, GlAx.unif_spec]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' ValuativeRel.uniformizer_lt_one.le hn) hN
  have hj' : Tendsto (fun n : ℕ => (j (unif k : k)) ^ n) atTop (nhds 0) := by
    have := (hj.tendsto 0).comp hv
    simpa [Function.comp_def, map_pow] using this
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hj'

end Emb

section Pow

variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (w : Plc L)

private theorem pow_ne (h : (L →+* Qbar l) → ℤ) :
    algPow w h ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L) ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion L →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 (Units.ne_zero _))

private theorem pow_anti {h h' : (L →+* Qbar l) → ℤ} (hh : ∀ τ, h τ ≤ h' τ) :
    ‖algPow w h' ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L)‖ ≤
      ‖algPow w h ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L)‖ := by
  classical
  haveI : Finite {j : w.adicCompletion L →+* Qbar l // Continuous j} :=
    GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion L →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, norm_prod, norm_prod]
  refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
  rw [norm_zpow, norm_zpow]
  have hlt := norm_unif_lt (k := w.adicCompletion L) (l := l) j.1 j.2
  have hpos : 0 < ‖j.1 ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L)‖ :=
    norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr (Units.ne_zero _))
  exact zpow_le_zpow_right_of_le_one₀ hpos hlt.le (hh _)

private theorem card_dvd (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) : l ∣ Nat.card 𝓀[w.adicCompletion L] := by
  have hc : Nat.card 𝓀[w.adicCompletion L] = Nat.card (𝓞 L ⧸ w.asIdeal) := by
    have := GlobalTheory.LocLanglands.resCard_eq_normV (E := L) w
    simpa [GlobalTheory.SplitWeil.resCard, Formalism.ConjugateSelfDual.normV] using this
  rw [hc]
  haveI := w.isPrime
  have hz : ((l : ℕ) : 𝓞 L ⧸ w.asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := w.asIdeal)).mpr hl
    simpa using this
  have hdvd : addOrderOf (1 : 𝓞 L ⧸ w.asIdeal) ∣ l := by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    simpa [nsmul_eq_mul] using hz
  have hord : addOrderOf (1 : 𝓞 L ⧸ w.asIdeal) = l := by
    rcases (Nat.dvd_prime (Fact.out : l.Prime)).mp hdvd with h | h
    · have h1 := addOrderOf_nsmul_eq_zero (1 : 𝓞 L ⧸ w.asIdeal)
      rw [h, one_nsmul] at h1
      exact absurd h1 one_ne_zero
    · exact h
  rw [← hord]
  exact addOrderOf_dvd_natCard _

private theorem norm_card_lt (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ‖((Nat.card 𝓀[w.adicCompletion L] : ℕ) : Qbar l)‖ < 1 := by
  obtain ⟨m, hm⟩ := card_dvd w hl
  rw [hm, Nat.cast_mul, ← map_natCast (algebraMap ℚ_[l] (Qbar l)) l,
    ← map_natCast (algebraMap ℚ_[l] (Qbar l)) m, ← map_mul]
  have he : ‖algebraMap ℚ_[l] (Qbar l) ((l : ℚ_[l]) * (m : ℚ_[l]))‖ = ‖(l : ℚ_[l]) * (m : ℚ_[l])‖ :=
    PadicAlgCl.norm_extends l _
  rw [he, norm_mul]
  have hm1 : ‖(m : ℚ_[l])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := l) (m : ℤ)
  calc ‖(l : ℚ_[l])‖ * ‖(m : ℚ_[l])‖ ≤ ‖(l : ℚ_[l])‖ * 1 :=
        mul_le_mul_of_nonneg_left hm1 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact Padic.norm_p_lt_one

end Pow

private theorem prod_le {M : Type} [CommMonoid M] {n : ℕ} (f : ℕ → M) (j : Fin n) :
    ∏ i with i ≤ j, f (i : ℕ) = ∏ k ∈ Finset.range (j + 1), f k := by
  classical
  refine Finset.prod_nbij (fun i : Fin n => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_range]
    have : (i : ℕ) ≤ (j : ℕ) := hi
    omega
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    show k ≤ (j : ℕ)
    omega
  · intro i _
    rfl

private theorem prod_tele {U : ℕ → ℂ} (h : ∀ k, U k ≠ 0) (m : ℕ) :
    ∏ k ∈ Finset.range m, U (k + 1) / U k = U m / U 0 := by
  induction m with
  | zero => simp [h 0]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [h m, h 0]

private theorem exp_core {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (a : Fin n → Qbar l) (u : Fin n → ℂ) (q : ℕ)
    (ha : ∀ i, a i ≠ 0) (hanti : ∀ i i', i ≤ i' → ‖a i'‖ ≤ ‖a i‖) (hq0 : (q : Qbar l) ≠ 0)
    (hq1 : ‖(q : Qbar l)‖ < 1) (hu : ∀ j, ‖ι.symm (u j)‖ = 1) :
    ∃ ω : Fin n → ℂˣ, Function.Injective ω ∧ ∀ j : Fin n,
      ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1, a i) * u j =
        ∏ i with i ≤ j, (ω i : ℂ) * ((q : ℂ) ^ (i : ℕ))⁻¹ := by
  classical
  have hq0' : (q : ℂ) ≠ 0 := by
    intro h
    apply hq0
    have : q = 0 := by exact_mod_cast h
    simp [this]
  have hqpos : 0 < ‖(q : Qbar l)‖ := norm_pos_iff.mpr hq0
  let A : ℕ → Qbar l := fun k => if h : k < n then a ⟨k, h⟩ else 1
  let W : ℕ → Qbar l := fun k => if h : k < n then ι.symm (u ⟨k, h⟩) else 1
  have hAne : ∀ k, A k ≠ 0 := by
    intro k
    by_cases h : k < n
    · simp only [A, dif_pos h]; exact ha _
    · simp only [A, dif_neg h]; exact one_ne_zero
  have hWn : ∀ k, ‖W k‖ = 1 := by
    intro k
    by_cases h : k < n
    · simp only [W, dif_pos h]; exact hu _
    · simp only [W, dif_neg h]; exact norm_one
  have hWne : ∀ k, W k ≠ 0 := fun k => norm_ne_zero_iff.mp (by rw [hWn k]; exact one_ne_zero)
  let T : ℕ → Qbar l := fun k =>
    (∏ i ∈ Finset.range (k + 1), A i) * W k * ∏ i ∈ Finset.range (k + 1), (q : Qbar l) ^ i
  have hTne : ∀ k, T k ≠ 0 := by
    intro k
    refine mul_ne_zero (mul_ne_zero ?_ (hWne k)) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => hAne i
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hq0
  let Tm : ℕ → Qbar l := fun k => if k = 0 then 1 else T (k - 1)
  have hTm0 : Tm 0 = 1 := by simp [Tm]
  have hTms : ∀ k, Tm (k + 1) = T k := by intro k; simp [Tm]
  have hTmne : ∀ k, Tm k ≠ 0 := by
    intro k
    rcases k with _ | k
    · rw [hTm0]; exact one_ne_zero
    · rw [hTms]; exact hTne k
  let U : ℕ → ℂ := fun k => ι (Tm k)
  have hUne : ∀ k, U k ≠ 0 := fun k => (_root_.map_ne_zero ι).mpr (hTmne k)
  let ω : Fin n → ℂˣ := fun i =>
    Units.mk0 (U ((i : ℕ) + 1) / U i) (div_ne_zero (hUne _) (hUne _))
  let G : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, (‖A i‖ * ‖(q : Qbar l)‖ ^ i)
  have hGs : ∀ k, G (k + 1) = G k * (‖A k‖ * ‖(q : Qbar l)‖ ^ k) :=
    fun k => Finset.prod_range_succ _ _
  have hG : ∀ k, k ≤ n → ‖Tm k‖ = G k := by
    intro k hk
    rcases k with _ | k
    · rw [hTm0, norm_one]; rfl
    · rw [hTms]
      simp only [T, G, norm_mul, norm_prod, norm_pow, hWn k, mul_one, Finset.prod_mul_distrib]
  have hGne : ∀ k, G k ≠ 0 := by
    intro k
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      mul_ne_zero (norm_ne_zero_iff.mpr (hAne i)) (pow_ne_zero _ hqpos.ne')
  have hnorm : ∀ i : Fin n, ‖ι.symm (ω i : ℂ)‖ = ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ) := by
    intro i
    have e1 : ι.symm (ω i : ℂ) = Tm ((i : ℕ) + 1) / Tm i := by
      simp only [ω, Units.val_mk0, U, map_div₀, RingEquiv.symm_apply_apply]
    rw [e1, norm_div, hG _ (Nat.succ_le_of_lt i.isLt), hG _ i.isLt.le, hGs,
      mul_div_cancel_left₀ _ (hGne _)]
    simp only [A, dif_pos i.isLt]
  have hsa : StrictAnti (fun i : Fin n => ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ)) := by
    intro i i' hii
    have h1 : ‖a i'‖ ≤ ‖a i‖ := hanti i i' hii.le
    have h2 : ‖(q : Qbar l)‖ ^ (i' : ℕ) < ‖(q : Qbar l)‖ ^ (i : ℕ) :=
      pow_lt_pow_right_of_lt_one₀ hqpos hq1 (Fin.lt_iff_val_lt_val.mp hii)
    have h3 : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    calc ‖a i'‖ * ‖(q : Qbar l)‖ ^ (i' : ℕ) ≤ ‖a i‖ * ‖(q : Qbar l)‖ ^ (i' : ℕ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ < ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ) := mul_lt_mul_of_pos_left h2 h3
  refine ⟨ω, ?_, ?_⟩
  · intro i i' h
    apply hsa.injective
    show ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ) = ‖a i'‖ * ‖(q : Qbar l)‖ ^ (i' : ℕ)
    rw [← hnorm i, ← hnorm i', h]
  · intro j
    have hL : (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1, a i) =
        ∏ k ∈ Finset.range (j + 1), A k := by
      rw [← prod_le A j]
      refine Finset.prod_congr ?_ ?_
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> intro h
        · exact Fin.le_iff_val_le_val.mpr (by omega)
        · have := Fin.le_iff_val_le_val.mp h
          omega
      · intro i _
        simp only [A, dif_pos i.isLt]
    have hR : (∏ i with i ≤ j, (ω i : ℂ) * ((q : ℂ) ^ (i : ℕ))⁻¹) =
        ∏ k ∈ Finset.range (j + 1), (U (k + 1) / U k * ((q : ℂ) ^ k)⁻¹) :=
      prod_le (fun k => U (k + 1) / U k * ((q : ℂ) ^ k)⁻¹) j
    have hWj : ι (W j) = u j := by simp only [W, dif_pos j.isLt, RingEquiv.apply_symm_apply]
    have hqp : (∏ k ∈ Finset.range (j + 1), (q : ℂ) ^ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ hq0'
    have hUj : U ((j : ℕ) + 1) =
        ι (∏ k ∈ Finset.range (j + 1), A k) * u j * ∏ k ∈ Finset.range (j + 1), (q : ℂ) ^ k := by
      simp only [U, hTms, T, map_mul, hWj, map_prod, map_pow, map_natCast]
    have hU0 : U 0 = 1 := by simp only [U, hTm0, map_one]
    rw [hL, hR, Finset.prod_mul_distrib, prod_tele hUne, Finset.prod_inv_distrib, hUj, hU0,
      div_one, mul_assoc _ (∏ k ∈ Finset.range (j + 1), (q : ℂ) ^ k), mul_inv_cancel₀ hqp, mul_one]

end UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.slope :
    Slope := by
  intro L Ω _ _ _ _ _ l _ n c H hA ι lam v u hu
  have hl := hA.Sl_over v
  obtain ⟨ω, h1, h2⟩ := exp_core ι
    (fun i => algPow (H.Sl v) (lowW lam i) ((unif ((H.Sl v).adicCompletion L) : ((H.Sl v).adicCompletion L)ˣ) : (H.Sl v).adicCompletion L))
    u (Nat.card 𝓀[(H.Sl v).adicCompletion L]) (fun i => pow_ne _ _)
    (fun i i' h => pow_anti _ fun τ => (lam τ).anti (Fin.rev_le_rev.2 h))
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') (norm_card_lt _ hl) hu
  exact ⟨ω, h1, fun j => h2 j⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PartRep
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

private theorem val_eq {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {F : M} (h0 : F ≠ 0) {a b : ℂ}
    (h : T F = a • F) (hg : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hg
  have hp : ∀ k : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ k) F = (a - b) ^ k • F := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, LinearMap.smul_apply,
        Module.End.one_apply, ← sub_smul, smul_smul, pow_succ]
  rw [hp k] at hk
  rcases smul_eq_zero.1 hk with h1 | h1
  · exact sub_eq_zero.1 (by_contra fun h2 => pow_ne_zero k h2 h1)
  · exact absurd h1 h0

private theorem chi_map {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (D : W.GDet n R G) (f : R →+* S) (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra R (Polynomial S) := ((algebraMap S (Polynomial S)).comp f).toAlgebra
  let φ : Polynomial R →ₐ[R] Polynomial S :=
    { Polynomial.mapRingHom f with commutes' := fun b => Polynomial.map_C f }
  refine Eq.trans ?_ (D.nat (Polynomial R) (Polynomial S) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)))
  change D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]

private theorem pol_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n q : ℕ) (a : ℕ → R) (b : ℕ → S)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp

private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

end UpperTheory.V.Z.J.D
end
end

