module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveClassFunctionExpansionRootSumsStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0020
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.CountExpandMap
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem count_expand_map (c : ℕ → ℕ) (m k : ℕ) (K : List ℕ) (hK : K.Nodup) :
    (expand (K.map fun j => (c j, j))).count (m, k) = if m = 1 ∧ k ∈ K then c k else 0 := by
  induction K with
  | nil => simp [UpperTheory.Gal.InertialTypesAlt.expand]
  | cons a K ih =>
    rw [List.nodup_cons] at hK
    have ih' := ih hK.2
    simp only [UpperTheory.Gal.InertialTypesAlt.expand, List.map_cons, List.flatMap_cons, List.count_append] at ih' ⊢
    rw [ih', List.count_replicate]
    by_cases hm : m = 1 <;> by_cases hk : k = a <;> simp_all <;> intros <;> subst_vars <;> simp_all

theorem UpperTheory.Gal.InertialTypesAlt.group1 :
    Group1 := by
  intro L₀ hpos
  have hmemK : ∀ k, k ∈ ((L₀.filter fun p => p.1 = 1).map Prod.snd).dedup ↔ (1, k) ∈ L₀ := by
    intro k
    simp only [List.mem_dedup, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨q, ⟨hq, hq1⟩, rfl⟩
      have hq' : q = (1, q.2) := Prod.ext (by simpa using hq1) rfl
      rw [← hq']
      exact hq
    · intro h
      exact ⟨(1, k), ⟨h, by simp⟩, rfl⟩
  refine ⟨(((L₀.filter fun p => p.1 = 1).map Prod.snd).dedup).map fun j => (L₀.count (1, j), j),
    ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    have h1 : (1, j) ∈ L₀ := (hmemK j).1 hj
    exact ⟨List.count_pos_iff.2 h1, h1⟩
  · rw [List.map_map]
    simpa [Function.comp_def] using List.nodup_dedup ((L₀.filter fun p => p.1 = 1).map Prod.snd)
  · rw [List.perm_iff_count]
    rintro ⟨m, k⟩
    rw [List.count_append, count_expand_map _ m k _ (List.nodup_dedup _)]
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hf : (m, k) ∉ L₀.filter (fun p => decide (2 ≤ p.1)) := by
        simp only [List.mem_filter, decide_eq_true_eq, not_and]
        intro _ h2
        omega
      rw [List.count_eq_zero_of_not_mem hf]
      interval_cases m
      · have h0 : (0, k) ∉ L₀ := fun h => absurd (hpos _ h) (lt_irrefl 0)
        simp [List.count_eq_zero_of_not_mem h0]
      · by_cases h : (1, k) ∈ L₀
        · simp [(hmemK k).2 h]
        · have h' : k ∉ ((L₀.filter fun p => p.1 = 1).map Prod.snd).dedup :=
            fun hk => h ((hmemK k).1 hk)
          simp [h', List.count_eq_zero_of_not_mem h]
    · rw [List.count_filter (by simpa using hm)]
      have hm1 : m ≠ 1 := by omega
      simp [hm1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PAvgMap
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.avgMap :
    AvgMap := by
  intro G _ _ H U Z W X _ _ _ _ _ _ _ _ ρ κ η Φ ev ψ hΦ hev hinj hψ hne
  haveI := Fintype.ofFinite G
  refine ⟨∑ g : G, (ρ g⁻¹).comp (Φ.comp (ψ.comp (η g))), ?_, ?_⟩
  · obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (LinearMap.ext h)
    intro h0
    have h1 := congrArg (fun L => ev (L x)) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
      LinearMap.zero_apply, map_zero] at h1
    have key : ∀ g : G, ev (ρ g⁻¹ (Φ (ψ (η g x)))) = if g ∈ H then ev (Φ (ψ x)) else 0 := by
      intro g
      split_ifs with hg
      · have e1 := hψ ⟨g, hg⟩ x
        have e2 := hΦ ⟨g, hg⟩ (ψ x)
        simp only at e1 e2
        rw [e1, e2, Representation.inv_self_apply]
      · exact hev g⁻¹ (by simpa using hg) _
    rw [Finset.sum_congr rfl (fun g _ => key g), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const] at h1
    have hc : (Finset.univ.filter (· ∈ H)).card ≠ 0 := by
      rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
      exact ⟨1, by simp [H.one_mem]⟩
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact hc (by exact_mod_cast h1)
    · exact hx (hinj _ h1)
  · intro k x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulRight k) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulRight, map_mul, Module.End.mul_apply, mul_inv_rev,
      Representation.self_inv_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspFrob
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open GlobalTheory.CuspGL GlobalTheory.BI
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem pow_mod_modEq (q m : ℕ) (hq : 0 < q) (hm : 0 < m) (e : ℕ) :
    q ^ e ≡ q ^ (e % m) [MOD q ^ m - 1] := by
  have h1 : q ^ m ≡ 1 [MOD q ^ m - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hq)
  conv_lhs => rw [← Nat.div_add_mod e m, pow_add, pow_mul]
  calc (q ^ m) ^ (e / m) * q ^ (e % m) ≡ 1 ^ (e / m) * q ^ (e % m) [MOD q ^ m - 1] :=
        (h1.pow _).mul_right _
    _ = q ^ (e % m) := by rw [one_pow, one_mul]

private theorem count_le (q m c c' i k : ℕ) (hq : 0 < q) (hm : 0 < m)
    (h : c' ≡ c * q ^ i [MOD q ^ m - 1]) :
    ((Finset.range m).filter fun j => c' * q ^ j ≡ k [MOD q ^ m - 1]).card ≤
      ((Finset.range m).filter fun j => c * q ^ j ≡ k [MOD q ^ m - 1]).card := by
  apply Finset.card_le_card_of_injOn (fun j => (j + i) % m)
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj ⊢
    refine ⟨Nat.mod_lt _ hm, ?_⟩
    calc c * q ^ ((j + i) % m) ≡ c * q ^ (j + i) [MOD q ^ m - 1] :=
          ((pow_mod_modEq q m hq hm (j + i)).symm).mul_left _
      _ = c * q ^ i * q ^ j := by ring
      _ ≡ c' * q ^ j [MOD q ^ m - 1] := h.symm.mul_right _
      _ ≡ k [MOD q ^ m - 1] := hj.2
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
    have h' : a ≡ b [MOD m] := Nat.ModEq.add_right_cancel' i hab
    unfold Nat.ModEq at h'
    rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h'

private theorem count_eq (q m c c' i k : ℕ) (hq : 0 < q) (hm : 0 < m)
    (h : c' ≡ c * q ^ i [MOD q ^ m - 1]) :
    ((Finset.range m).filter fun j => c' * q ^ j ≡ k [MOD q ^ m - 1]).card =
      ((Finset.range m).filter fun j => c * q ^ j ≡ k [MOD q ^ m - 1]).card := by
  apply le_antisymm (count_le q m c c' i k hq hm h)
  apply count_le q m c' c (m - i % m) k hq hm
  have hr : i % m < m := Nat.mod_lt _ hm
  have hd : m * (i / m) + i % m = i := Nat.div_add_mod i m
  have hs : i + (m - i % m) = m * (i / m + 1) := by
    rw [mul_add, mul_one]
    omega
  calc c = c * q ^ ((i + (m - i % m)) % m) := by rw [hs, Nat.mul_mod_right, pow_zero, mul_one]
    _ ≡ c * q ^ (i + (m - i % m)) [MOD q ^ m - 1] :=
        ((pow_mod_modEq q m hq hm _).symm).mul_left _
    _ = c * q ^ i * q ^ (m - i % m) := by ring
    _ ≡ c' * q ^ (m - i % m) [MOD q ^ m - 1] := h.symm.mul_right _

private theorem psi_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    (hn : 0 < Module.finrank F V) (c c' i : ℕ)
    (h : c' ≡ c * Nat.card F ^ i [MOD Nat.card F ^ Module.finrank F V - 1])
    (g : Module.End F V) (hg : IsUnit g) :
    psi (rootSum θ c') V g = psi (rootSum θ c) V g := by
  have hcl : ∀ s : F[X] → ℂ, IsAdditive s →
      IsClassFn (psi s V) ∧ GlobalTheory.CuspGL.IsPrimitive (psi s V) := fun s hs =>
    ⟨fun e x => _root_.GlobalTheory.CuspGL.psi_conj F s V V e x, _root_.GlobalTheory.CuspGL.isPrimitive_psi F V s hs⟩
  have hc := hcl _ (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ c).1
  have hc' := hcl _ (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ c').1
  have e1 := GlobalTheory.T.primitiveClassFunction_expansion_rootSums F V θ hθ _ hc'.1 hc'.2 hn g hg
  have e2 := GlobalTheory.T.primitiveClassFunction_expansion_rootSums F V θ hθ _ hc.1 hc.2 hn g hg
  have hsum : (∑ k ∈ Finset.range (Nat.card F ^ Module.finrank F V - 1),
      (ipGL (psi (rootSum θ c') V) fun x ↦ rootSum θ k (LinearMap.charpoly x)) *
        psi (rootSum θ k) V g) =
      ∑ k ∈ Finset.range (Nat.card F ^ Module.finrank F V - 1),
      (ipGL (psi (rootSum θ c) V) fun x ↦ rootSum θ k (LinearMap.charpoly x)) *
        psi (rootSum θ k) V g := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn, GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn,
      count_eq (Nat.card F) (Module.finrank F V) c c' i k Nat.card_pos hn h]
  have hne : glCard F (Module.finrank F V) * (Module.finrank F V : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ (Nat.cast_ne_zero.mpr hn.ne')
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact mul_left_cancel₀ hne (e1.trans (hsum.trans e2.symm))

theorem UpperTheory.Gal.InertialTypesAlt.cuspFrob :
    CuspFrob := by
  intro F _ _ θ hθ m c c' i hm h
  funext x
  simp only [GlobalTheory.Shin.cusp, GlobalTheory.Shin.psiG]
  congr 1
  have hr : Module.finrank F (Fin m → F) = m := Module.finrank_fin_fun F
  refine psi_eq F (Fin m → F) θ hθ (by rw [hr]; exact hm) c c' i (by rw [hr]; exact h) _ ?_
  exact x.isUnit.map
    (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) F ≃ₐ[F] Module.End F (Fin m → F))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PDetPair
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem detc_isCl {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ) :
    IsCl (detc θ t c) := by
  intro x y
  simp only [detc, Units.val_mul, Matrix.det_mul]
  congr 2
  rw [mul_comm _ (x : Matrix (Fin t) (Fin t) F).det, mul_assoc, ← Matrix.det_mul, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]

private theorem detc_ne_zero {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ)
    (x : GL (Fin t) F) : detc θ t c x ≠ 0 := by
  unfold detc
  apply pow_ne_zero
  have hx : (x : Matrix (Fin t) (Fin t) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero
  have ha : algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det ≠ 0 :=
    (_root_.map_ne_zero _).mpr hx
  intro h
  have h1 : θ (algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det *
      (algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det)⁻¹) = 1 := by
    rw [mul_inv_cancel₀ ha, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem detc_parab {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ)
    (hd : ∑ _i : Fin t, 1 = t) (p : parab F (stdBlocks (fun _ : Fin t => 1) hd)) :
    detc θ t c (p : GL (Fin t) F) =
      ∏ i, detc θ 1 c (leviProj F (stdBlocks (fun _ : Fin t => 1) hd) p i) := by
  have h := congrArg Units.val (det_parab F (stdBlocks (fun _ : Fin t => 1) hd) p)
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod] at h
  simp only [detc, h, map_prod, Finset.prod_pow]

theorem UpperTheory.Gal.InertialTypesAlt.detPair :
    FrobL → JDEq → DetPair := by
  intro hF hJ F _ _ θ t c
  obtain ⟨hJD, hcusp, _⟩ := hJ F θ
  have hd : ∑ _i : Fin t, 1 = t := by simp
  obtain ⟨c', hc', hfr⟩ := hF F t (fun _ => 1) t hd
  have hJt : J θ (List.replicate t (1, c)) t =
      hcL (List.ofFn fun _ : Fin t => (⟨1, detc θ 1 c⟩ : (m : ℕ) × (GL (Fin m) F → ℂ))) t := by
    rw [← JD_nil, hJD]
    congr 1
    simp [hcusp, List.map_replicate, List.ofFn_const]
  unfold Pairs
  rw [hJt, hfr _ _ (detc_isCl θ t c), mul_ne_zero_iff]
  refine ⟨hc', ?_⟩
  simp_rw [← detc_parab θ t c hd]
  haveI : Fintype (parab F (stdBlocks (fun _ : Fin t => 1) hd)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  intro h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hpos : ∀ p : parab F (stdBlocks (fun _ : Fin t => 1) hd),
      0 < (star (detc θ t c (p : GL (Fin t) F)) * detc θ t c (p : GL (Fin t) F)).re := by
    intro p
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr (detc_ne_zero θ t c _)
  have : 0 < ∑ p : parab F (stdBlocks (fun _ : Fin t => 1) hd),
      (star (detc θ t c (p : GL (Fin t) F)) * detc θ t c (p : GL (Fin t) F)).re :=
    Finset.sum_pos (fun p _ => hpos p) ⟨1, Finset.mem_univ _⟩
  linarith
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PHcChar
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.hcChar :
    HcChar := by
  intro F _ _ a b n hn A B hA hB
  exact GlobalTheory.T.harishChandraInductionGL_isCharacter F a b n hn A B hA hB
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PHcOne
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem toG_one' {F : Type} [Field F] (m : ℕ) :
    toG (1 : Matrix (Fin m) (Fin m) F) = 1 := by
  unfold toG
  rw [dite_eq_left isUnit_one]
  exact Units.ext (IsUnit.unit_spec _)

private theorem ent_one' {F : Type} [Field F] {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) :
    ent (1 : Matrix (Fin n) (Fin n) F) i j = if i = j then 1 else 0 := by
  unfold ent
  rw [dite_eq_left ⟨hi, hj⟩, Matrix.one_apply]
  simp only [Fin.mk.injEq]

private theorem tlG_one' {F : Type} [Field F] (a b : ℕ) :
    tlG a (1 : GL (Fin (a + b)) F) = 1 := by
  have h : tl a ((1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    show ent _ (i : ℕ) (j : ℕ) = _
    rw [Units.val_one, ent_one' _ _ (lt_of_lt_of_le i.isLt (Nat.le_add_right a b))
      (lt_of_lt_of_le j.isLt (Nat.le_add_right a b))]
    simp only [Fin.val_inj]
  unfold tlG
  rw [h, toG_one']

private theorem brG_one' {F : Type} [Field F] (a b : ℕ) :
    brG a b (1 : GL (Fin (a + b)) F) = 1 := by
  have h : br a b ((1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    show ent _ (a + (i : ℕ)) (a + (j : ℕ)) = _
    rw [Units.val_one, ent_one' _ _ (Nat.add_lt_add_left i.isLt a)
      (Nat.add_lt_add_left j.isLt a)]
    simp only [Nat.add_left_cancel_iff, Fin.val_inj]
  unfold brG
  rw [h, toG_one']

private theorem inPar_one' {F : Type} [Field F] (a n : ℕ) : InPar a (1 : GL (Fin n) F) := by
  intro i j hj hi
  rw [Units.val_one, Matrix.one_apply_ne]
  intro h
  rw [h] at hi
  omega

private theorem gal_id' {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) :
    gal (RingHom.id F) n y = y := by
  ext i j
  rfl

theorem UpperTheory.Gal.InertialTypesAlt.hcOne :
    HcOne := by
  intro F _ _ a b n hn α β hα hβ
  subst hn
  unfold hc hcTw
  simp only [gal_id', mul_one, inv_mul_cancel, inPar_one', ite_true, tlG_one', brG_one']
  haveI : Nonempty { p : GL (Fin (a + b)) F // InPar a p } := ⟨⟨1, inPar_one' a _⟩⟩
  haveI : Fintype (GL (Fin (a + b)) F) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, nsmul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
    (mul_ne_zero (Nat.cast_ne_zero.mpr Finset.univ_nonempty.card_pos.ne') (mul_ne_zero hα hβ))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PJdChar
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem detc_isChar {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t k : ℕ) :
    GlobalTheory.BI.IsChar ℂ ℂ (detc θ t k) := by
  let χ : GL (Fin t) F →* ℂ := (powMonoidHom k).comp (θ.comp
    ((algebraMap F (AlgebraicClosure F)).toMonoidHom.comp
      ((Units.coeHom F).comp Matrix.GeneralLinearGroup.det)))
  refine ⟨1, (algebraMap ℂ (Module.End ℂ (Fin 1 → ℂ))).toMonoidHom.comp χ, fun g => ?_⟩
  simp [Representation.character, χ, detc, Module.algebraMap_end_eq_smul_id, LinearMap.trace_id]

private theorem jd_isChar (hH : HcChar) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (L : List (ℕ × ℕ)) (hL : GlobalTheory.BI.IsChar ℂ ℂ (J θ L (deg L))) (D : List (ℕ × ℕ)) :
    GlobalTheory.BI.IsChar ℂ ℂ (JD θ D L (deg D + deg L)) := by
  induction D with
  | nil =>
    have e : deg ([] : List (ℕ × ℕ)) + deg L = deg L := by simp [GlobalTheory.Shin.deg]
    rw [e, JD_nil]
    exact hL
  | cons p D ih =>
    rw [JD_cons]
    refine hH F p.1 (deg D + deg L) _ ?_ _ _ (detc_isChar θ p.1 p.2) ih
    simp [GlobalTheory.Shin.deg, add_assoc]

theorem UpperTheory.Gal.InertialTypesAlt.jdChar :
    HcChar → JDChar := by
  intro hH F _ _ θ hθ
  refine ⟨detc_isChar θ, fun a hok hq => ?_⟩
  obtain ⟨-, -, hL⟩ := hok
  have hJ := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F θ hθ a.L (fun p hp => by rw [← hq]; exact hL p hp) _ rfl
  exact jd_isChar hH θ a.L hJ a.D
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftDet
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_gal {A B : Type} [Field A] [Field B] (f : A →+* B) (n : ℕ) (x : GL (Fin n) A) :
    ((gal f n x : GL (Fin n) B) : Matrix (Fin n) (Fin n) B).det = f (x : Matrix (Fin n) (Fin n) A).det := by
  rw [RingHom.map_det]
  rfl

private theorem pow_apply_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') (q : ℕ)
    (hs : ∀ z, s z = z ^ q) (i : ℕ) (z : F') : (s ^ i) z = z ^ (q ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, hs, ← pow_mul, pow_succ]

private theorem det_nrmG {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') (q : ℕ)
    (hs : ∀ z, s z = z ^ q) (t l : ℕ) (δ : GL (Fin t) F') :
    ((nrmG (galAct F F' t) s l δ : GL (Fin t) F') : Matrix (Fin t) (Fin t) F').det =
      (δ : Matrix (Fin t) (Fin t) F').det ^ ∑ i ∈ Finset.range l, q ^ i := by
  induction l with
  | zero => simp [nrmG]
  | succ l ih =>
    have h : nrmG (galAct F F' t) s (l + 1) δ =
        nrmG (galAct F F' t) s l δ * galAct F F' t (s ^ l) δ := by
      simp [nrmG, List.range_succ]
    rw [h, Units.val_mul, Matrix.det_mul, ih, galAct_apply, det_gal, Finset.sum_range_succ, pow_add]
    congr 1
    exact pow_apply_eq s q hs l _

theorem UpperTheory.Gal.InertialTypesAlt.liftDet :
    LiftDet := by
  intro F F' _ _ _ _ s hs ι θ t k hN
  funext δ
  unfold shLift
  rw [dite_eq_left (hN δ)]
  have hγ : IsNorm s δ (hN δ).choose := (hN δ).choose_spec
  generalize (hN δ).choose = γ at hγ
  have h1 : ((incl F F' t γ : GL (Fin t) F') : Matrix (Fin t) (Fin t) F').det =
      ((nrm s δ : GL (Fin t) F') : Matrix (Fin t) (Fin t) F').det := by
    have h := congrArg Units.val (isConj_iff_eq.1 ((Matrix.GeneralLinearGroup.det).map_isConj hγ))
    simpa using h
  have h2 : algebraMap F F' (γ : Matrix (Fin t) (Fin t) F).det =
      (δ : Matrix (Fin t) (Fin t) F').det ^ ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i := by
    rw [← det_nrmG s (Nat.card F) hs t _ δ]
    have h3 := det_gal (algebraMap F F') t γ
    rw [← h3]
    exact h1
  have h4 : pullθ ι θ (algebraMap F (AlgebraicClosure F) (γ : Matrix (Fin t) (Fin t) F).det) =
      θ (algebraMap F' (AlgebraicClosure F') (algebraMap F F' (γ : Matrix (Fin t) (Fin t) F).det)) := by
    change θ (ι _) = _
    rw [ι.commutes, IsScalarTower.algebraMap_apply F F' (AlgebraicClosure F')]
  simp only [detc]
  rw [h4, h2, map_pow, map_pow, ← pow_mul, mul_comm]
end

