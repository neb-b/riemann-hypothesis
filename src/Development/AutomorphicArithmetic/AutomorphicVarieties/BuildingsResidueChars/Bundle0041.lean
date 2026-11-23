module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RealSpanOfGoodRealForm
section
open UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA in
theorem UpperTheory.real_span_of_good_real_form :
    UpperTheory.V.Af.BA.RePart → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.GoodRe → UpperTheory.V.Af.BA.SpanRe := by
  intro hRP hRI hG L _ _ _ N σ hσ p t ht
  apply spanpsd
  intro k hk hzero
  obtain ⟨k', hk'q, hk'P⟩ := hRP L N σ hσ k
  obtain ⟨hk'psd, hk'0⟩ := hk'P hk
  apply hk'0
  refine ConeExtensionAcyclic.simp_span (hG L N σ hσ).locFin p t ht k' hk'psd ?_
  intro y hy
  have hM : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (y : Lat L N) = 1 := by
    intro j
    have := hy j
    rw [qr_apply] at this
    exact this
  have hinvq : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (sLat σ (y : Lat L N)) = 1 := by
    intro j
    rw [((hRI L N σ hσ).2 _ (t j).1.2).1 (y : Lat L N)]
    exact hM j
  rw [qr_apply, hk'q, hzero _ hM, hzero _ hinvq]
  norm_num
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RealStructureActionOfRealInvolution
section
open NumberField UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA

set_option maxHeartbeats 1000000 in
theorem UpperTheory.real_structure_action_of_real_involution :
    UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.ActRe := by
  intro hR L _ _ N σ hσ
  have hHR : ∀ (g : Fix N σ) (h : HR L N), (g : Gm L N) • (h : HS L N) ∈ HR L N :=
    fun g h => ((hR L N σ hσ).2 h h.2).2 g g.2
  have hinv : ∀ (g : Fix N σ) (h : HS L N), ((g⁻¹ : Fix N σ) : Gm L N) • (g : Gm L N) • h = h := by
    intro g h
    rw [← mul_smul, Subgroup.coe_inv, inv_mul_cancel, one_smul]
  have hinv' : ∀ (g : Fix N σ) (h : HS L N), (g : Gm L N) • ((g⁻¹ : Fix N σ) : Gm L N) • h = h := by
    intro g h
    rw [← mul_smul, Subgroup.coe_inv, mul_inv_cancel, one_smul]
  let E : Fix N σ → (HR L N ≃L[ℝ] HR L N) := fun g =>
    LinearEquiv.toContinuousLinearEquiv
      { toFun := fun h => ⟨(g : Gm L N) • (h : HS L N), hHR g h⟩
        invFun := fun h => ⟨((g⁻¹ : Fix N σ) : Gm L N) • (h : HS L N), hHR g⁻¹ h⟩
        map_add' := by
          intro a b
          apply Subtype.ext
          simp only [Submodule.coe_add]
          rw [← actL_apply, ← actL_apply, ← actL_apply, map_add (f := _)]
        map_smul' := by
          intro c a
          apply Subtype.ext
          simp only [Submodule.coe_smul, RingHom.id_apply]
          rw [← actL_apply, ← actL_apply, map_smul]
        left_inv := by
          intro h
          apply Subtype.ext
          exact hinv g h
        right_inv := by
          intro h
          apply Subtype.ext
          exact hinv' g h }
  have hE : ∀ (g : Fix N σ) (h : HR L N), ((E g h : HR L N) : HS L N) = (g : Gm L N) • (h : HS L N) :=
    fun g h => rfl
  let π : Fix N σ → (NZ L N ≃ NZ L N) := fun g =>
    { toFun := fun y => ⟨(g : Gm L N) • (y : Lat L N), smul_ne_zero_lat _ y.2⟩
      invFun := fun y => ⟨((g⁻¹ : Fix N σ) : Gm L N) • (y : Lat L N), smul_ne_zero_lat _ y.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        show ((g⁻¹ : Fix N σ) : Gm L N) • (g : Gm L N) • (y : Lat L N) = y
        rw [← mul_smul, Subgroup.coe_inv, inv_mul_cancel, one_smul]
      right_inv := by
        intro y
        apply Subtype.ext
        show (g : Gm L N) • ((g⁻¹ : Fix N σ) : Gm L N) • (y : Lat L N) = y
        rw [← mul_smul, Subgroup.coe_inv, mul_inv_cancel, one_smul] }
  have hq : ∀ (g : Fix N σ) (y : NZ L N) (h : HR L N), (qr L N (π g y)) (E g h) = (qr L N y) h := by
    intro g y h
    rw [qr_apply, qr_apply, hE]
    show q ((g : Gm L N) • (h : HS L N)) ((g : Gm L N) • (y : Lat L N)) = q (h : HS L N) (y : Lat L N)
    rw [q_smul, ← mul_smul, inv_mul_cancel, one_smul]
  have hT : ∀ (g : Fix N σ) (k : HR L N), E g k ∈ Tr L N ↔ k ∈ Tr L N := by
    intro g k
    constructor
    · intro hk
      change ((E g k : HR L N) : HS L N) ∈ Psd L N at hk
      rw [hE] at hk
      have h1 := smul_mem_Psd ((g : Gm L N))⁻¹ hk
      rw [← mul_smul, inv_mul_cancel, one_smul] at h1
      exact h1
    · intro hk
      show ((E g k : HR L N) : HS L N) ∈ Psd L N
      rw [hE]
      exact smul_mem_Psd _ hk
  have key := fun g => ConeExtensionAcyclic.simp_smul (E g) (π g) (hq g) (hT g)
  let inst : MulAction (Fix N σ) (ConeExtensionAcyclic.Vert (qr L N)) :=
    { smul := fun g v => ⟨E g v.1, (key g).1 v.1 v.2⟩
      one_smul := by
        intro v
        apply Subtype.ext
        apply Subtype.ext
        show ((1 : Fix N σ) : Gm L N) • ((v.1 : HR L N) : HS L N) = _
        rw [OneMemClass.coe_one, one_smul]
      mul_smul := by
        intro g g' v
        apply Subtype.ext
        apply Subtype.ext
        show ((g * g' : Fix N σ) : Gm L N) • ((v.1 : HR L N) : HS L N) =
          (g : Gm L N) • (g' : Gm L N) • ((v.1 : HR L N) : HS L N)
        rw [Subgroup.coe_mul, mul_smul] }
  refine ⟨inst, fun g v => rfl, ?_⟩
  intro n g t ht
  exact (key g).2 n t _ (fun j => rfl) ht
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepHomAlternatingSumEqZero
section
open CategoryTheory UpperTheory.V.Af.BA in
private def repHomEvalLinearMap {Γ : Type} [Group Γ] {A B : Rep.{0} ℂ Γ} (x : A) : (A ⟶ B) →ₗ[ℂ] B where
  toFun φ := φ.hom x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.rep_hom_alternating_sum_eq_zero :
    UpperTheory.V.Af.BA.AltZero := by
  intro Γ I _ _ K
  have key : ∀ (p : ℕ) (t : K.Tup p), (K.alt p).hom (Finsupp.single t 1) =
      ((p + 1).factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin (p + 1)),
        ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ) := by
    intro p t
    show repHomEvalLinearMap (B := PC Γ (K.Tup p)) (Finsupp.single t (1 : ℂ)) (K.alt p) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Cx.alt, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro π _
    congr 1
    exact Cx.reC_single K _ t 1
  refine ⟨?_, ?_⟩
  · apply PC_ext
    intro x
    rw [key 0 x]
    have hre : K.re (id : Fin 1 → Fin 1) x = x := Subtype.ext rfl
    simp [Fintype.sum_unique, hre]
  · intro p hp
    apply PC_ext
    intro t
    rw [key p t]
    have hnt := hp t
    simp only [Function.Injective, not_forall] at hnt
    obtain ⟨a, b, htab, hab⟩ := hnt
    have ht : ∀ y, Subtype.val t (Equiv.swap a b y) = Subtype.val t y := by
      intro y
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, htab]
      · rw [h2, htab]
      · rfl
    set S := ∑ π : Equiv.Perm (Fin (p + 1)),
      ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ) with hSdef
    have hS : S = -S := by
      conv_lhs => rw [hSdef, ← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))]
      rw [hSdef, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro π _
      have hre : K.re (⇑((Equiv.mulLeft (Equiv.swap a b)) π)) t = K.re π t :=
        Subtype.ext (funext fun k => by simp [Cx.re, Equiv.Perm.mul_apply, ht])
      rw [hre, Equiv.coe_mulLeft, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      push_cast
      rw [neg_one_mul, neg_smul]
    have hS0 : S = 0 := self_eq_neg.1 hS
    rw [hS0, smul_zero]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepResolutionExists
section
open CategoryTheory

namespace UpperTheory.V.Af.BA.ResolutionExactness

variable {Γ : Type} [Group Γ]

private theorem comp_zero_of {A B C : Rep.{0} ℂ Γ} {f : A ⟶ B} {g : B ⟶ C}
    (h : Function.Exact f.hom g.hom) : f ≫ g = 0 := by
  ext x
  exact h.apply_apply_eq_zero x

private theorem exact_of {A B C : Rep.{0} ℂ Γ} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
    (h : Function.Exact f.hom g.hom) : (ShortComplex.mk f g w).Exact := by
  exact (forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _
    ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => (h x).1 hx)

set_option backward.isDefEq.respectTransparency false in
private theorem main : UpperTheory.V.Af.BA.ResOf := by
  intro Γ _ X d ε hX hε h0 hd
  have hdd : ∀ p, d (p + 1) ≫ d p = 0 := fun p => comp_zero_of (hd p)
  let K : ChainComplex (Rep ℂ Γ) ℕ := ChainComplex.of X d hdd
  have hK : ∀ j, K.d (j + 1) j = d j := fun j => by simp [K]
  have hK0 : K.d 1 0 ≫ ε = 0 := by
    rw [hK 0]
    exact comp_zero_of h0
  let π : K ⟶ (ChainComplex.single₀ (Rep ℂ Γ)).obj (Rep.trivial ℂ Γ ℂ) :=
    (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hK0⟩
  have hπ0 : π.f 0 = ε := by simp [π]
  let P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ) :=
    { complex := K
      projective := hX
      π := π
      quasiIso := ⟨fun n => by
        cases n with
        | zero =>
          rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
          · refine ⟨exact_of _ ?_, ?_⟩
            · show Function.Exact (K.d 1 0).hom (π.f 0).hom
              rw [hπ0, hK 0]
              exact h0
            · show Epi (π.f 0)
              rw [hπ0, Rep.epi_iff_surjective]
              exact hε
          all_goals rfl
        | succ m =>
          rw [quasiIsoAt_iff_exactAt']
          · rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
            refine exact_of _ ?_
            show Function.Exact (K.d (m + 2) (m + 1)).hom (K.d (m + 1) m).hom
            rw [hK, hK]
            exact hd m
          · apply ChainComplex.exactAt_succ_single_obj⟩ }
  refine ⟨P, fun p => ⟨Iso.refl _⟩, fun e he0 he => ?_⟩
  refine ⟨ChainComplex.ofHom (X := K) (Y := K) e (fun i => by rw [hK]; exact he i), ?_, fun p hp => hp⟩
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  ext1
  simp [P, hπ0, he0]

end UpperTheory.V.Af.BA.ResolutionExactness

theorem UpperTheory.repResolution_exists :
    UpperTheory.V.Af.BA.ResOf :=
  UpperTheory.V.Af.BA.ResolutionExactness.main
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleRestrictionToNormalSubgroup
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

private theorem UpperTheory.V.Af.Cr.semisimple_restriction_normal {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K Γ V) (N : Subgroup Γ) (hN : N.Normal)
    (hss : ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule K V, (∀ g, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W')
    (W : Submodule K V) (hW : ∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) :
    ∃ W' : Submodule K V, (∀ g ∈ N, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W' := by
  have hmul : ∀ (a b : Γ) (v : V), ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v; rw [map_mul]; rfl
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', hW's, hW'd, ?_⟩
  rw [codisjoint_iff]
  obtain ⟨C, hCs, hC⟩ := hss (⨅ g : Γ, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    rw [hmul]; exact hv _)
  by_cases hC0 : C = ⊥
  · have hU := hC.sup_eq_top
    rw [hC0, sup_bot_eq] at hU
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : Γ, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    simpa using hv 1
  exfalso
  obtain ⟨S, ⟨hSs, hS0, hSC⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥ ∧ U ≤ C)
    ⟨C, fun g _ v hv => hCs g v hv, hC0, le_rfl⟩
  have hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W' := by
    intro n hn v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)
  have key : ∀ g : Γ, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    by_cases hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥
    · have hle : W' ⊔ S.map (ρ g) ≤ W' := by
        refine hmax ⟨?_, ?_⟩ le_sup_left
        · intro n hn v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          rw [map_add (f := _)]
          refine Submodule.add_mem_sup (hW's n hn a ha) ?_
          refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩
          rw [hmul, hmul]; congr 2; group
        · rw [Submodule.disjoint_def]
          intro v hvW hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          have h1 : ρ g s ∈ W ⊔ W' := by
            have := (W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)
            simpa using this
          have h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g) := ⟨hs, h1⟩
          rw [hA, Submodule.mem_bot] at h2
          subst h2
          rw [map_zero, add_zero] at hvW ⊢
          exact Submodule.disjoint_def.mp hW'd a hvW ha
      intro s hs
      exact Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))
    · have hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g) := by
        refine hmin ⟨?_, hA, inf_le_left.trans hSC⟩ inf_le_left
        intro n hn v hv
        refine ⟨hSs n hn v hv.1, ?_⟩
        have h1 : ρ g v ∈ W ⊔ W' := hv.2
        have h2 := hsup _ (hN.conj_mem n hn g) _ h1
        show ρ g (ρ n v) ∈ W ⊔ W'
        rw [hmul] at h2 ⊢
        have : g * n * g⁻¹ * g = g * n := by group
        rwa [this] at h2
      intro s hs
      exact (hle hs).2
  apply hS0
  rw [eq_bot_iff, ← hC.inf_eq_bot]
  intro s hs
  refine ⟨?_, hSC hs⟩
  have : s ∈ (⨅ g : Γ, (W ⊔ W').comap (ρ g)) := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => key g s hs
  exact this

theorem UpperTheory.semisimple_restriction_to_normal_subgroup :
    UpperTheory.V.Af.Cr.SSRes := by
  intro Γ Γ' k _ _ _ n r φ hN hss W hW
  let ρ : Representation k Γ (Fin n → k) :=
    { toFun := fun g => Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k)
      map_one' := by simp; rfl
      map_mul' := fun a b => by rw [map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl }
  obtain ⟨W', h1, h2⟩ := UpperTheory.V.Af.Cr.semisimple_restriction_normal ρ φ.range hN (fun U hU => hss U hU) W (by
    rintro _ ⟨g, rfl⟩ v hv
    exact hW g v hv)
  exact ⟨W', fun g v hv => h1 (φ g) ⟨g, rfl⟩ v hv, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TiltFrobeniusTeichmullerAction
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module Topology Polynomial

namespace UpperTheory.V.Af.Wd

variable {l : ℕ} [hl : Fact l.Prime]

open scoped Formalism.Per in
private theorem tf_lift (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∃ (z : OC l) (x : Om l), (z : ℂ_[l]) = (x : ℂ_[l]) ∧ x ^ l ^ m = x ∧
      PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  have hz : y.untilt ^ l ^ m = y.untilt := by rw [← map_pow, hy]
  have hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l) := by
    have := congrArg (fun t : OC l => (t : ℂ_[l])) hz
    simpa using this
  have hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l]) := by
    refine ⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩
    simp [hz']
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one (Om l) _
    (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))
  refine ⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩
  apply (algebraMap (Om l) ℂ_[l]).injective
  have hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l) := hx
  rw [map_pow, hx', hz']

private theorem tf_act {P : LocPrime l} (AI : LocAinf l P) (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y)
    {z : OC l} {x : Om l} (hzx : (z : ℂ_[l]) = (x : ℂ_[l]))
    (h0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z)
    (g : GQ l) (k : ℕ) (hg : g x = x ^ k) : AI.actT g y = y ^ k := by
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g y 0 _ h0
  rw [hzx, AI.actC_ext, hg, PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx] at h1
  have h3 : y' = z ^ k := Subtype.ext (by rw [h1]; simp)
  refine GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hy])
    (by rw [← pow_mul, mul_comm, pow_mul, hy]) ?_
  rw [h2, map_pow, h0, h3]
  exact map_pow _ _ _

private theorem tf_root {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ l ^ m = x) (h0 : x ≠ 0) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ x ^ n = 1 := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  refine ⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩
  · have h2 := (Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]

end UpperTheory.V.Af.Wd

open UpperTheory.V.Af.Wd in
theorem UpperTheory.tilt_frobenius_teichmuller_action :
    UpperTheory.V.Af.Wd.TiltFrob := by
  intro l hl y m hm hy g k hg
  obtain ⟨z, x, hzx, hx, h0⟩ := tf_lift y hm hy
  refine tf_act _ y hm hy hzx h0 g (l ^ k) ?_
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, zero_pow (pow_ne_zero _ hl.out.ne_zero)]
  obtain ⟨n, hn0, hn, hxn⟩ := tf_root hm hx hx0
  have hmem : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨n, hn0, hn, hxn⟩
  have h1 := hg ⟨x, hmem⟩
  rw [GlobalTheory.Pst.frobUr_pow_root k ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn)] at h1
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneDpstLeftExact
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

private theorem tensV_eq_rT {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem UpperTheory.weilDeligne_dpst_leftExact :
    UpperTheory.V.Af.Wd.DLeft := by
  intro l _ P K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hex0
  have hex : Function.Exact (f.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := hex0
  have hexT := Module.Flat.rTensor_exact (Bst P) hex
  have hinj : Function.Injective ((f.restrictScalars ℚ_[l]).rTensor (Bst P)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hfi
  refine ⟨fun x y hxy => Subtype.ext (hinj ?_), fun y => ⟨fun hy => ?_, ?_⟩⟩
  · rw [← tensV_eq_rT, ← tensV_eq_rT]
    exact congrArg Subtype.val hxy
  · have h0 : tensV P p (y : V ⊗[ℚ_[l]] Bst P) = 0 := congrArg Subtype.val hy
    rw [tensV_eq_rT] at h0
    obtain ⟨z, hz⟩ := (hexT _).mp h0
    have hz' : tensV P f z = y := by rw [tensV_eq_rT]; exact hz
    obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
    have hzD : z ∈ Dpst P ρ' := by
      refine (mem_Dpst P ρ').mpr ⟨K', fun g hg => hinj ?_⟩
      rw [← tensV_eq_rT, ← tensV_eq_rT, tensV_stRep P ρ' ρ f hf, hz', hK' g hg]
    exact ⟨⟨z, hzD⟩, Subtype.ext hz'⟩
  · rintro ⟨x, rfl⟩
    refine Subtype.ext ?_
    show tensV P p (tensV P f x.1) = 0
    rw [tensV_eq_rT, tensV_eq_rT]
    exact (hexT _).mpr ⟨x.1, rfl⟩
end

