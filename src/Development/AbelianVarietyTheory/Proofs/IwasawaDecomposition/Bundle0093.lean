module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FgSpanTopOfLatticeCompatibleSemilinear
section
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem oLatTie_fg_span_top : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  intro K _ _ _ n σ O _ φO W _ _ M j N hli hT
  classical
  obtain ⟨hgen, hmem⟩ := hT
  have hj : ∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
    intro x
    conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ]
    simp
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hj] at hx
    have h0 := Fintype.linearIndependent_iff.1 hli _ hx
    funext i
    exact σ.injective (by simpa using h0 i)
  have hgen' : ∀ v, ∃ x, v ∈ M.gen → j x = v := by
    intro v
    by_cases hv : v ∈ M.gen
    · obtain ⟨x, hx⟩ := hgen v hv
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose pre hpre using hgen'
  have hN : N = Submodule.span (𝓞 K) (pre '' (M.gen : Set W)) := by
    ext x
    rw [hmem, Submodule.mem_span_image_finset_iff_exists_fun']
    refine exists_congr fun a => ?_
    have : ∑ v ∈ M.gen, σ ((a v : 𝓞 K) : K) • v = j (∑ v ∈ M.gen, a v • pre v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul K (a v) (pre v), map_smulₛₗ, hpre v hv]
    rw [this]
    exact ⟨fun h => (hinj h).symm, fun h => congrArg j h.symm⟩
  refine ⟨hN ▸ Submodule.fg_span ((M.gen.finite_toSet).image pre), ?_⟩
  rw [hN]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  let B := Module.Basis.span hli
  let F0 := B.constr ℂ (fun i => σ (f (Pi.single i 1)))
  obtain ⟨F, hFF⟩ := LinearMap.exists_extend F0
  have hFe : ∀ i, F (j (Pi.single i 1)) = σ (f (Pi.single i 1)) := by
    intro i
    have h1 : (B i : W) = j (Pi.single i 1) := by simp [B, Module.Basis.span_apply hli i]
    rw [← h1]
    have h2 := LinearMap.congr_fun hFF (B i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [F0]
  have hF : ∀ x, F (j x) = σ (f x) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hj, map_sum]
    conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFe]
    simp
  have hF0 : F = 0 := by
    apply LinearMap.ext_on M.span_top
    intro v hv
    rw [← hpre v hv, hF]
    have : f (pre v) ∈ (⊥ : Submodule K K) := by
      rw [← hf]
      exact Submodule.mem_map_of_mem
        (Submodule.subset_span (Submodule.subset_span ⟨v, hv, rfl⟩))
    rw [(Submodule.mem_bot K).1 this]
    simp
  apply hf0
  refine LinearMap.ext fun x => σ.injective ?_
  rw [← hF, hF0]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc Polynomial
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.InvCris

section Abstract
variable {k Ω B D : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing B] [CommRing D]
  {U : IntermediateField k Ω} {ι : B →+* D} {O : Ω →+* D} {u : U →+* B} {φ : B →+* B} {σ : U →ₐ[k] U}

theorem aeval_step [Nontrivial D] (hι : Function.Injective ι) (hu : ∀ c : U, ι (u c) = O c)
    (hφ : ∀ c : U, φ (u c) = u (σ c)) {b : B} {y y' : Ω} (hy : ι b = O y) (hy' : ι (φ b) = O y')
    (q : k[X]) (hq : aeval y q = 0) : aeval y' q = 0 := by
  set v : k →+* B := u.comp (algebraMap k U) with hv
  have e1 : ι.comp v = O.comp (algebraMap k Ω) := by
    ext c
    simp [hv, hu]
  have e2 : φ.comp v = v := by
    ext c
    simp [hv, hφ]
  have key : ∀ (x : B) (z : Ω), ι x = O z → ι (q.eval₂ v x) = O (aeval z q) := by
    intro x z h
    rw [aeval_def, hom_eval₂, hom_eval₂, e1, h]
  have h0 : q.eval₂ v b = 0 := hι (by rw [key b y hy, hq, map_zero, map_zero])
  have h1 : q.eval₂ v (φ b) = 0 := by
    have := congrArg φ h0
    rwa [hom_eval₂, e2, map_zero] at this
  apply O.injective
  rw [← key _ _ hy', h1, map_zero, map_zero]

theorem periodic [Nontrivial D] [Algebra.IsAlgebraic k Ω] (hι : Function.Injective ι)
    (hu : ∀ c : U, ι (u c) = O c) (hφ : ∀ c : U, φ (u c) = u (σ c)) (S : AddSubgroup B)
    (hS : ∀ b ∈ S, φ b ∈ S) (hO : ∀ b ∈ S, ∃ y, ι b = O y) {b : B} (hb : b ∈ S) :
    ∃ N, 0 < N ∧ φ^[N] b = b := by
  have hint : ∀ y : Ω, IsIntegral k y := fun y => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hit : ∀ (i : ℕ) (x : B), x ∈ S → φ^[i] x ∈ S := by
    intro i x hx
    induction i with
    | zero => exact hx
    | succ i ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  have hinj0 : ∀ x ∈ S, φ x = 0 → x = 0 := by
    intro x hx h
    obtain ⟨y, hy⟩ := hO x hx
    have := aeval_step hι hu hφ hy (y' := 0) (by rw [h, map_zero, map_zero]) _ (minpoly.aeval k y)
    rw [← coeff_zero_eq_aeval_zero', map_eq_zero, minpoly.coeff_zero_eq_zero (hint y)] at this
    exact hι (by rw [hy, this, map_zero, map_zero])
  have hinj : ∀ (i : ℕ) (x : B), x ∈ S → φ^[i] x = φ^[i] b → x = b := by
    intro i
    induction i with
    | zero => exact fun x _ h => h
    | succ i ih =>
      intro x hx h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
      refine ih x hx (sub_eq_zero.1 (hinj0 _ (S.sub_mem (hit i x hx) (hit i b hb)) ?_))
      rw [map_sub, h, sub_self]
  choose y hy using fun i : ℕ => hO _ (hit i b hb)
  have hroot : ∀ i, aeval (y i) (minpoly k (y 0)) = 0 := by
    intro i
    induction i with
    | zero => exact minpoly.aeval k _
    | succ i ih =>
      exact aeval_step hι hu hφ (hy i) (by rw [← hy (i + 1), Function.iterate_succ_apply']) _ ih
  obtain ⟨i, j, hij, h⟩ := (Polynomial.rootSet_finite (minpoly k (y 0)) Ω).exists_lt_map_eq_of_forall_mem
    (f := y) (fun i => (Polynomial.mem_rootSet_of_ne (minpoly.ne_zero (hint _))).2 (hroot i))
  refine ⟨j - i, Nat.sub_pos_of_lt hij, hinj i _ (hit _ _ hb) ?_⟩
  rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hij.le]
  exact hι (by rw [hy, hy, h])

theorem mem_range (hu : ∀ c : U, ι (u c) = O c) (hφ : ∀ c : U, φ (u c) = u (σ c))
    (fund : ∀ (b : B) (y : Ω), φ b = b → ι b = O y → ∃ c : k, u (algebraMap k U c) = b)
    {b : B} {N : ℕ} (hN : 0 < N) (hb : φ^[N] b = b) (hO : ∀ i, ∃ y, ι (φ^[i] b) = O y)
    {ζ : U} (hζ : σ^[N] ζ = ζ) (hζ' : ∀ i, 0 < i → i < N → σ^[i] ζ ≠ ζ) : ∃ c, u c = b := by
  choose y hy using hO
  have tr : ∀ n : ℕ, ∑ i ∈ Finset.range N, u ((σ^[i] ζ) ^ n) * φ^[i] b ∈ u.range := by
    intro n
    obtain ⟨c, hc⟩ := fund (∑ i ∈ Finset.range N, u ((σ^[i] ζ) ^ n) * φ^[i] b)
      (∑ i ∈ Finset.range N, (((σ^[i] ζ) ^ n : U) : Ω) * y i) (by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        have e : ∀ i, φ (u ((σ^[i] ζ) ^ n) * φ^[i] b) = u ((σ^[i + 1] ζ) ^ n) * φ^[i + 1] b := by
          intro i
          rw [map_mul, hφ, map_pow σ, Function.iterate_succ_apply', Function.iterate_succ_apply']
        simp only [e]
        have h1 := Finset.sum_range_succ (fun i => u ((σ^[i] ζ) ^ n) * φ^[i] b) N
        have h2 := Finset.sum_range_succ' (fun i => u ((σ^[i] ζ) ^ n) * φ^[i] b) N
        rw [h1, hζ, hb] at h2
        exact (add_right_cancel h2).symm) (by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul, hu, hy])
    exact ⟨_, hc⟩
  have pol : ∀ p : U[X], ∑ i ∈ Finset.range N, u (p.eval (σ^[i] ζ)) * φ^[i] b ∈ u.range := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [eval_add, map_add (f := _), add_mul, Finset.sum_add_distrib]
      exact add_mem hp hq
    | monomial n a =>
      simp only [eval_monomial, map_mul, mul_assoc, ← Finset.mul_sum]
      exact mul_mem ⟨a, rfl⟩ (tr n)
  obtain ⟨c, hc⟩ := pol (∏ j ∈ (Finset.range N).erase 0, (X - C (σ^[j] ζ)))
  rw [Finset.sum_eq_single 0] at hc
  · have hne : (∏ j ∈ (Finset.range N).erase 0, (X - C (σ^[j] ζ))).eval (σ^[0] ζ) ≠ 0 := by
      rw [eval_prod]
      refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
      rw [Finset.mem_erase, Finset.mem_range] at hj
      simpa [sub_eq_zero] using (hζ' j (Nat.pos_of_ne_zero hj.1) hj.2).symm
    refine ⟨((∏ j ∈ (Finset.range N).erase 0, (X - C (σ^[j] ζ))).eval (σ^[0] ζ))⁻¹ * c, ?_⟩
    rw [map_mul, hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
    rfl
  · intro i hi hi0
    rw [eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hi0, hi⟩) (by simp), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 hN) h

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem exists_period (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) {N : ℕ} (hN : 0 < N) :
    ∃ ζ : ↥(MaximalUnramifiedExtension l), σ^[N] ζ = ζ ∧ ∀ i, 0 < i → i < N → σ^[i] ζ ≠ ζ := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have h1 : 1 < l ^ N := Nat.one_lt_pow hN.ne' hl
  have hm : 0 < l ^ N - 1 := by omega
  have hd : ¬ l ∣ l ^ N - 1 := by
    intro h
    have h2 : l ∣ l ^ N := dvd_pow_self l hN.ne'
    have := (Nat.dvd_sub h2 h)
    rw [Nat.sub_sub_self h1.le, Nat.dvd_one] at this
    omega
  haveI : NeZero ((l ^ N - 1 : ℕ) : Om l) := ⟨by exact_mod_cast hm.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ N - 1)
  have hzm : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, hm, hd, hz.pow_eq_one⟩
  set ζ : ↥(MaximalUnramifiedExtension l) := ⟨z, hzm⟩ with hζ
  have hp : IsPrimitiveRoot ζ (l ^ N - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := (MaximalUnramifiedExtension l).val) hz Subtype.val_injective
  have hit : ∀ i, σ^[i] ζ = ζ ^ l ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, map_pow, hσ ζ _ hm hd hp.pow_eq_one, ← pow_mul, pow_succ']
  have hz0 : ζ ≠ 0 := hp.ne_zero hm.ne'
  have hpw : ∀ i, ζ ^ l ^ i = ζ ^ (l ^ i - 1) * ζ := by
    intro i
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
  refine ⟨ζ, by rw [hit, hpw, hp.pow_eq_one, one_mul], fun i hi hiN h => ?_⟩
  rw [hit, hpw, mul_eq_right₀ hz0] at h
  have h3 : 1 < l ^ i := Nat.one_lt_pow hi.ne' hl
  have h4 : l ^ i < l ^ N := Nat.pow_lt_pow_right hl hiN
  exact hp.pow_ne_one_of_pos_of_lt (by omega) (by omega) h

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem invariants_Bcris : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.Bcris l),
    (∀ g ∈ GK K, Per.σB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ C.u c = b := by
  intro l _ C K b hb
  obtain ⟨hφ, -, -, hι, hσ, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  have hcomm := (_root_.GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.1
  have hfil := (_root_.GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.2 0
  rcases subsingleton_or_nontrivial (Per.BdR l) with hs | hs
  · exact ⟨0, zero_mem _, hι (Subsingleton.elim _ _)⟩
  let O : Om l →+* Per.BdR l := (algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o
  have hu : ∀ c : ↥(MaximalUnramifiedExtension l), C.ι (C.u c) = O c := C.ι_u
  let S : AddSubgroup (Per.Bcris l) :=
    { carrier := {x | ∀ g ∈ GK K, Per.σB g x = x}
      zero_mem' := fun g _ => map_zero _
      add_mem' := fun {x y} hx hy g hg => by rw [map_add (f := _), hx g hg, hy g hg]
      neg_mem' := fun {x} hx g hg => by rw [map_neg, hx g hg] }
  have hS : ∀ x ∈ S, Per.φB l x ∈ S := fun x hx g hg => by rw [← hcomm, hx g hg]
  have hO' : ∀ x ∈ S, ∃ y ∈ K.1, C.ι x = O y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := GlobalTheory.T.bdR_galois_invariants_eq_finExt l C K (C.ι x) (fun g hg => by rw [← hσ, hx g hg])
    exact ⟨y, hy, e.symm⟩
  have hO : ∀ x ∈ S, ∃ y, C.ι x = O y := fun x hx => (hO' x hx).imp fun _ h => h.2
  have fund : ∀ (x : Per.Bcris l) (y : Om l), Per.φB l x = x → C.ι x = O y →
      ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = x := by
    intro x y h1 h2
    refine GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp l C x h1 ?_
    rw [h2]
    refine (hfil (C.o y)).2 ?_
    have hone : (1 : Per.BdRp l) ∈ Per.FilP l 0 :=
      (hfil 1).1 (by rw [map_one]; exact (_root_.GlobalTheory.MemLoc.filD_laws l).2.1)
    simpa using Ideal.mul_mem_left _ (C.o y) hone
  have hbS : b ∈ S := hb
  obtain ⟨N, hN, hper⟩ := periodic hι hu hφ S hS hO hbS
  obtain ⟨ζ, h1, h2⟩ := exists_period C.σ C.σ_root hN
  have hit : ∀ i, (Per.φB l)^[i] b ∈ S := by
    intro i
    induction i with
    | zero => rw [Function.iterate_zero_apply]; exact hbS
    | succ i ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  obtain ⟨c, hc⟩ := mem_range hu hφ fund hN hper (fun i => hO _ (hit i)) h1 h2
  obtain ⟨y, hy, e⟩ := hO' b hbS
  refine ⟨c, ?_, hc⟩
  have : (c : Om l) = y := O.injective (by rw [← hu, hc, e])
  rwa [this]

end GlobalTheory.MemLoc.InvCris
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Filter Topology

namespace GlobalTheory.Mem.UnrAe

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.finiteSingle L v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Function.update (fun _ => 1) v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Function.update_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_const.update v continuous_id
  have := (RestrictedProduct.continuous_inclusion hle).comp hf
  exact this

theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

theorem tendsto_finSingle (y : ∀ v : HeightOneSpectrum (𝓞 L), v.adicCompletion L) (hy : ∀ v, Valued.v (y v) ≤ 1) :
    Tendsto (fun v => Neutral.B1.finiteSingle L v (y v)) cofinite (𝓝 1) := by
  classical
  let A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w => w.adicCompletionIntegers L
  let o : ∀ w, A w := fun w => ⟨1, one_mem (w.adicCompletionIntegers L)⟩
  let g : HeightOneSpectrum (𝓞 L) → ∀ w, A w := fun v => Function.update o v ⟨y v, hy v⟩
  have hg : Tendsto g cofinite (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with v hv
    have h' : w ≠ v := fun h => hv h.symm
    exact (Function.update_of_ne h' _ _).symm
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  refine Tendsto.congr (fun v => ?_) h2
  apply Subtype.ext
  funext w
  show (g v w : w.adicCompletion L) = Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (y v) w
  by_cases hw : w = v
  · subst hw; simp [g]
  · simp [g, o, Function.update_of_ne hw]

theorem tendsto_localIdele (x : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ) (hx : ∀ v, IsUnitAt v (x v)) :
    Tendsto (fun v => Neutral.B1.localIdele L v (x v)) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  have h1 := tendsto_finSingle (fun v => (x v : v.adicCompletion L)) fun v => (hx v).le
  have h2 := tendsto_finSingle (fun v => (((x v)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L)) fun v => by
    have h : Valued.v (x v : v.adicCompletion L) = 1 := hx v
    rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
  have h3 : Tendsto (fun v => ((Neutral.B1.localIdele L v (x v) : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h1
  have h4 : Tendsto (fun v => (((Neutral.B1.localIdele L v (x v))⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h2
  exact h3.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h4)

theorem isUnitAt_pow {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) (m : ℕ) :
    IsUnitAt v (x ^ m) := by
  unfold IsUnitAt at *
  rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]

theorem finite_ramified (χ : HChar L) : {v | ¬ χ.UnrAt v}.Finite := by
  have h : ∀ v, ∃ x : (v.adicCompletion L)ˣ, IsUnitAt v x ∧
      (‖((χ.loc v x : ℂˣ) : ℂ) - 1‖ < 1 / 2 → χ.UnrAt v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    exact (hc _ (isUnitAt_pow hx m)).1
  choose x hx hx' using h
  have hc : Continuous fun a : Neutral.B1.Ideles L => ‖((χ.1 a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp χ.2.1).sub continuous_const).norm
  have h1 := (hc.tendsto 1).comp (tendsto_localIdele x hx)
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact eventually_cofinite.1 (h2.mono fun v hv => hx' v hv)

theorem exists_levelLe (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : ∃ n, χ.LevelLe v n := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (χ.2.1.comp (continuous_localIdele v))).sub continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat, fun x hx hx1 => ?_⟩
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
  have h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)


open Classical in
theorem unr_ae_and_level : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), {v | ¬ χ.UnrAt v}.Finite ∧ ∀ v, ∃ n, χ.LevelLe v n :=
  fun _ _ _ χ => ⟨finite_ramified χ, exists_levelLe χ⟩

end GlobalTheory.Mem.UnrAe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionUnflattenStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linComb_pow_section_unflatten : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  first | exact @GlobalTheory.SecPowUnflat.unflat | exact GlobalTheory.SecPowUnflat.unflat | (intros; apply GlobalTheory.SecPowUnflat.unflat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCOfModEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr


open Classical in
theorem splitsC_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime →
    p ≡ 1 [MOD H.QS * H.q * H.d] → SplitsC H.E p := by
  intro R H p hp h
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hpos : 0 < H.QS * H.q * H.d := Nat.pos_of_ne_zero H.condN_ne_zero
  have hlt : 1 < H.QS * H.q * H.d :=
    lt_of_lt_of_le (by omega : 1 < H.d) (Nat.le_of_dvd hpos (dvd_mul_left _ _))
  refine (GlobalTheory.HostSplit.split_of_one_mod R H p hp ?_).1
  rw [h]
  exact Nat.mod_eq_of_lt hlt

end GlobalTheory.Mem.Chr
end

