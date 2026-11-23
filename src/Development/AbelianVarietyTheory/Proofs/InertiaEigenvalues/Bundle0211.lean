module

public import Mathlib
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionShapeOfTorsionCounts
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg.Shape

def kerProd {O : Type} [CommRing O] (c : O) {ι M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] :
    LinearMap.ker (c • LinearMap.id : (ι → M) × N →ₗ[O] (ι → M) × N) ≃
      (ι → LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) ×
        LinearMap.ker (c • LinearMap.id : N →ₗ[O] N) where
  toFun x := (fun i => ⟨x.1.1 i, by
      have h := LinearMap.mem_ker.1 x.2
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Prod.ext_iff, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, funext_iff, Pi.smul_apply, Pi.zero_apply] at h
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact h.1 i⟩, ⟨x.1.2, by
      have h := LinearMap.mem_ker.1 x.2
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Prod.ext_iff, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_zero, Prod.snd_zero] at h
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact h.2⟩)
  invFun y := ⟨(fun i => (y.1 i).1, y.2.1), by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, Prod.ext_iff,
        Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, funext_iff, Pi.smul_apply,
        Pi.zero_apply]
      refine ⟨fun i => ?_, ?_⟩
      · have := (y.1 i).2
        simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using this
      · have := y.2.2
        simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using this⟩
  left_inv x := rfl
  right_inv y := rfl

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem card_ker_prod [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ)
    {H : Type} [AddCommGroup H] [Module O H] {a : ℕ} {F : Type} [AddCommGroup F] [Module O F]
    (φ : H ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) (n : ℕ) :
    Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : H →ₗ[O] H)) =
      (Nat.card (IsLocalRing.ResidueField O) ^ n) ^ a *
        Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) := by
  have hK : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Formalism.NG.KO O →ₗ[O] Formalism.NG.KO O)) =
      Nat.card (IsLocalRing.ResidueField O) ^ n :=
    (levKO_card hϖ (LinearEquiv.refl O (Formalism.NG.KO O)) n).2
  have h1 : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : H →ₗ[O] H)) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id :
        (Fin a → Formalism.NG.KO O) × F →ₗ[O] (Fin a → Formalism.NG.KO O) × F)) :=
    Nat.card_congr (levCongr φ (ϖ ^ n))
  rw [h1, Nat.card_congr (kerProd (ϖ ^ n)), Nat.card_prod, Nat.card_fun, hK, Nat.card_eq_fintype_card (α := Fin a), Fintype.card_fin]

theorem cyclic_of_card_ker_le [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ)
    {F : Type} [AddCommGroup F] [Module O F] [Finite F]
    (h : Nat.card (LinearMap.ker (ϖ • LinearMap.id : F →ₗ[O] F)) ≤
      Nat.card (IsLocalRing.ResidueField O)) :
    ∃ c0 : F, ∀ y : F, ∃ a : O, y = a • c0 := by
  set g : F →ₗ[O] F := ϖ • LinearMap.id with hg
  have hQ : Nat.card (F ⧸ LinearMap.range g) ≤ Nat.card (IsLocalRing.ResidueField O) := by
    have e1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range g)
    have e2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g)
    have e3 := Nat.card_congr (LinearMap.quotKerEquivRange g).toEquiv
    have hr : 0 < Nat.card (LinearMap.range g) := Nat.card_pos
    rw [e3, e1, mul_comm (Nat.card (LinearMap.ker g))] at e2
    rw [Nat.eq_of_mul_eq_mul_left hr e2]
    exact h
  have hx : ∃ x : F, ∀ y : F, y ∈ Submodule.span O {x} ⊔ LinearMap.range g := by
    by_cases hs : Subsingleton (F ⧸ LinearMap.range g)
    · refine ⟨0, fun y => ?_⟩
      have : (Submodule.Quotient.mk y : F ⧸ LinearMap.range g) = 0 := Subsingleton.elim _ _
      exact Submodule.mem_sup_right ((Submodule.Quotient.mk_eq_zero _).1 this)
    · rw [not_subsingleton_iff_nontrivial] at hs
      haveI : Finite (F ⧸ LinearMap.range g) :=
        Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
      obtain ⟨xb, hxb⟩ := exists_ne (0 : F ⧸ LinearMap.range g)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
      set t := LinearMap.toSpanSingleton O (F ⧸ LinearMap.range g)
        (Submodule.Quotient.mk x) with ht
      have hker : LinearMap.ker t = IsLocalRing.maximalIdeal O := by
        symm
        apply (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le
        · intro htop
          apply hxb
          have h1 : (1 : O) ∈ LinearMap.ker t := htop ▸ Submodule.mem_top
          simpa [ht] using h1
        · rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
            LinearMap.mem_ker, ht, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
            Submodule.Quotient.mk_eq_zero]
          exact ⟨x, rfl⟩
      have hrange : LinearMap.range t = ⊤ := by
        by_contra hne
        obtain ⟨z, hz⟩ : ∃ z, z ∉ LinearMap.range t := by
          by_contra hall
          push_neg at hall
          exact hne (eq_top_iff.2 fun z _ => hall z)
        have hlt : Nat.card (LinearMap.range t) < Nat.card (F ⧸ LinearMap.range g) :=
          Finite.card_subtype_lt (p := fun w => w ∈ LinearMap.range t) hz
        have hc : Nat.card (LinearMap.range t) = Nat.card (IsLocalRing.ResidueField O) := by
          rw [← Nat.card_congr (LinearMap.quotKerEquivRange t).toEquiv, hker]
          rfl
        omega
      refine ⟨x, fun y => ?_⟩
      obtain ⟨a, ha⟩ : ∃ a, t a = Submodule.Quotient.mk y := by
        have hy : (Submodule.Quotient.mk y : F ⧸ LinearMap.range g) ∈ LinearMap.range t :=
          hrange ▸ Submodule.mem_top
        exact hy
      rw [ht, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.eq] at ha
      have hy : y = a • x - (a • x - y) := by abel
      rw [hy]
      exact Submodule.sub_mem _
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
        (Submodule.mem_sup_right ha)
  obtain ⟨x, hx⟩ := hx
  have hfg : (⊤ : Submodule O F).FG :=
    ⟨(Set.finite_univ (α := F)).toFinset, by simp⟩
  have hle : (⊤ : Submodule O F) ≤ Submodule.span O {x} := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro y _
    have hsub : LinearMap.range g ≤ IsLocalRing.maximalIdeal O • (⊤ : Submodule O F) := by
      rintro _ ⟨z, rfl⟩
      have hm : ϖ ∈ IsLocalRing.maximalIdeal O := by
        rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
      exact Submodule.smul_mem_smul hm Submodule.mem_top
    have hmono : Submodule.span O {x} ⊔ LinearMap.range g ≤
        Submodule.span O {x} ⊔ IsLocalRing.maximalIdeal O • (⊤ : Submodule O F) :=
      sup_le_sup_left hsub _
    exact hmono (hx y)
  refine ⟨x, fun y => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle Submodule.mem_top)
  exact ⟨a, ha.symm⟩

theorem quotShape_of_counts : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {X : Type} [AddCommGroup X] [Module O X] (Hc : Submodule O X) (d a : ℕ)
    {F : Type} [AddCommGroup F] [Module O F] [Finite F], (Hc ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) →
    (∃ C : ℕ, ∀ n : ℕ, 0 < n →
      Nat.card (IsLocalRing.ResidueField O) ^ (n * d) ≤ Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ∧
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ≤ C * Nat.card (IsLocalRing.ResidueField O) ^ (n * d)) →
    Nat.card (LinearMap.ker (ϖ ^ 1 • LinearMap.id : Hc →ₗ[O] Hc)) ≤ Nat.card (IsLocalRing.ResidueField O) ^ (d + 1) →
    Formalism.RepresentationBoundsCohomology.JT.QuotShape Hc ⊥ d := by
  intro O _ _ _ _ ϖ hϖ X _ _ Hc d a F _ _ _ φ hC h1
  have hq : 2 ≤ Nat.card (IsLocalRing.ResidueField O) := Finite.one_lt_card
  have hcard := card_ker_prod hϖ φ
  have hF1 : ∀ n : ℕ, 1 ≤ Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) :=
    fun n => Nat.card_pos
  have hFle : ∀ n : ℕ, Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) ≤ Nat.card F :=
    fun n => Nat.card_le_card_of_injective _ Subtype.val_injective
  obtain ⟨C, hC⟩ := hC
  have hlt : ∀ m : ℕ, m < Nat.card (IsLocalRing.ResidueField O) ^ m := fun m =>
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq m)
  have had : a = d := by
    rcases lt_trichotomy a d with h | h | h
    · exfalso
      have hn := (hC (Nat.card F + 1) (Nat.succ_pos _)).1
      rw [hcard] at hn
      set q := Nat.card (IsLocalRing.ResidueField O)
      set n := Nat.card F + 1
      have h2 : (q ^ n) ^ a * q ^ n ≤ q ^ (n * d) := by
        rw [← pow_succ, ← pow_mul]
        exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left n h)
      have hpos : 0 < (q ^ n) ^ a := by positivity
      have h3 : (q ^ n) ^ a * q ^ n ≤ (q ^ n) ^ a * Nat.card F :=
        h2.trans (hn.trans (Nat.mul_le_mul_left _ (hFle n)))
      have h4 := Nat.le_of_mul_le_mul_left h3 hpos
      have h5 := hlt n
      omega
    · exact h
    · exfalso
      have hn := (hC (C + 1) (Nat.succ_pos _)).2
      rw [hcard] at hn
      set q := Nat.card (IsLocalRing.ResidueField O)
      set n := C + 1
      have h2 : q ^ (n * d) * q ^ n ≤ (q ^ n) ^ a := by
        rw [← pow_add, ← pow_mul]
        exact Nat.pow_le_pow_right (by omega) (by nlinarith)
      have h3 : (q ^ n) ^ a ≤ (q ^ n) ^ a * Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) :=
        Nat.le_mul_of_pos_right _ (hF1 n)
      have hpos : 0 < q ^ (n * d) := by positivity
      have h4 : q ^ (n * d) * q ^ n ≤ q ^ (n * d) * C := by
        rw [mul_comm (q ^ (n * d)) C]; exact h2.trans (h3.trans hn)
      have h5 := Nat.le_of_mul_le_mul_left h4 hpos
      have h6 := hlt n
      omega
  subst had
  have hsoc : Nat.card (LinearMap.ker (ϖ • LinearMap.id : F →ₗ[O] F)) ≤
      Nat.card (IsLocalRing.ResidueField O) := by
    have h1' := h1
    rw [hcard 1] at h1'
    simp only [pow_one] at h1'
    rw [pow_succ] at h1'
    have hpos : 0 < Nat.card (IsLocalRing.ResidueField O) ^ a := by positivity
    have := Nat.le_of_mul_le_mul_left h1' hpos
    exact this
  obtain ⟨c0, hc0⟩ := cyclic_of_card_ker_le hϖ hsoc
  have hbot : (⊥ : Submodule O X).comap Hc.subtype = ⊥ := by
    rw [Submodule.comap_bot, Submodule.ker_subtype]
  let e0 : (Hc ⧸ (⊥ : Submodule O X).comap Hc.subtype) ≃ₗ[O] Hc :=
    Submodule.quotEquivOfEqBot _ hbot
  let ι : (Fin a → Formalism.NG.KO O) →ₗ[O] (Hc ⧸ (⊥ : Submodule O X).comap Hc.subtype) :=
    e0.symm.toLinearMap ∘ₗ φ.symm.toLinearMap ∘ₗ LinearMap.inl O _ F
  let π : (Hc ⧸ (⊥ : Submodule O X).comap Hc.subtype) →ₗ[O] F :=
    LinearMap.snd O _ F ∘ₗ φ.toLinearMap ∘ₗ e0.toLinearMap
  refine ⟨F, inferInstance, inferInstance, ι, π, ?_, ?_, c0, hc0⟩
  · intro u v huv
    have := congrArg (fun z => (φ (e0 z)).1) huv
    simpa only [ι, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.inl_apply] using this
  · intro y
    constructor
    · intro hy
      refine ⟨(φ (e0 y)).1, ?_⟩
      apply e0.injective
      apply φ.injective
      simp only [π, LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply,
        LinearEquiv.coe_coe] at hy
      simp only [ι, LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact Prod.ext rfl hy.symm
    · rintro ⟨u, rfl⟩
      simp only [ι, π, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.inl_apply, LinearMap.snd_apply]

end GlobalTheory.ShapeNeg.Shape
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
section
noncomputable section

namespace GlobalTheory.Cmp.WachMonoidal

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke

section Ext

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']

end Ext

section Crys

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem tensorB_comp (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) g (CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x) =
      CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (g.comp f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem tensorB_id (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (LinearMap.id : V →ₗ[LL] V) x = x := by
  simp [CrystallineSubrepresentation.tensorB]

theorem tensorB_zero (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (0 : V →ₗ[LL] V') x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]

theorem tensorB_add (f g : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (f + g) x =
      CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x + CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB, add_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; abel

theorem coe_DcrisMap {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : CrystallineSubrepresentation.IsEquivariant ρ ρ' f) (x : ↥(Dcris PD ρ)) :
    (CrystallineSubrepresentation.DcrisMap PD hf x : V' ⊗[Qp] B) = CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x := rfl

theorem isCrys_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  have h1 : CrystallineSubrepresentation.IsEquivariant ρ ρ' e.toLinearMap := he
  have h2 : CrystallineSubrepresentation.IsEquivariant ρ' ρ e.symm.toLinearMap := fun g x => by
    apply e.injective
    simp [he]
  let E : ↥(Dcris PD ρ) ≃ₗ[LL] ↥(Dcris PD ρ') :=
    LinearEquiv.ofLinear (CrystallineSubrepresentation.DcrisMap PD h1) (CrystallineSubrepresentation.DcrisMap PD h2)
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
  unfold IsCrys at h ⊢
  rw [← E.finrank_eq, ← e.finrank_eq, h]

theorem finite_Dcris [FiniteDimensional LL V] {ρ : Representation LL G V} (h : IsCrys PD ρ) :
    Module.Finite LL ↥(Dcris PD ρ) := by
  rcases Nat.eq_zero_or_pos (finrank LL ↥(Dcris PD ρ)) with h0 | h0
  · have := PD.finK₀
    have hK : 0 < finrank Qp K₀ := Module.finrank_pos
    unfold IsCrys at h
    have hV : finrank LL V = 0 := by
      rw [h0] at h
      rcases Nat.mul_eq_zero.mp h.symm with h | h
      · omega
      · exact h
    have : Subsingleton V := Module.finrank_zero_iff.mp hV
    infer_instance
  · exact Module.finite_of_finrank_pos h0

theorem isCrys_prod [FiniteDimensional LL V] [FiniteDimensional LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (h : IsCrys PD ρ) (h' : IsCrys PD ρ') : IsCrys PD (ρ.prod ρ') := by
  have := finite_Dcris PD h
  have := finite_Dcris PD h'
  have e1 : CrystallineSubrepresentation.IsEquivariant ρ (ρ.prod ρ') (LinearMap.inl LL V V') := fun g x => by
    simp [Representation.prod]
  have e2 : CrystallineSubrepresentation.IsEquivariant ρ' (ρ.prod ρ') (LinearMap.inr LL V V') := fun g x => by
    simp [Representation.prod]
  have p1 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ (LinearMap.fst LL V V') := fun g x => by
    simp [Representation.prod]
  have p2 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ' (LinearMap.snd LL V V') := fun g x => by
    simp [Representation.prod]
  let E : (↥(Dcris PD ρ) × ↥(Dcris PD ρ')) ≃ₗ[LL] ↥(Dcris PD (ρ.prod ρ')) :=
    LinearEquiv.ofLinear ((CrystallineSubrepresentation.DcrisMap PD e1).coprod (CrystallineSubrepresentation.DcrisMap PD e2))
      ((CrystallineSubrepresentation.DcrisMap PD p1).prod (CrystallineSubrepresentation.DcrisMap PD p2))
      (by
        refine LinearMap.ext fun x => Subtype.ext ?_
        simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
          Submodule.coe_add, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [← tensorB_add, show (LinearMap.inl LL V V').comp (LinearMap.fst LL V V') +
          (LinearMap.inr LL V V').comp (LinearMap.snd LL V V') = LinearMap.id by ext <;> simp,
          tensorB_id])
      (by
        refine LinearMap.ext fun x => Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, tensorB_id, tensorB_zero, add_zero]
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, tensorB_id, tensorB_zero, zero_add])
  unfold IsCrys at h h' ⊢
  rw [← E.finrank_eq, Module.finrank_prod, Module.finrank_prod, h, h', mul_add]

end Crys

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem isCrys_of_isSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L)
    (i' : LatHom T'.L T''.L) (h : IsCrys PD T.ρ) (h' : IsCrys PD T'.ρ) (hs : TensorLatticeUnitPart.IsSumLat i i') :
    IsCrys PD T''.ρ :=
  isCrys_of_equiv PD (LinearEquiv.ofBijective (i.f.coprod i'.f) hs.1)
    (fun g x => by simp [Representation.prod, i.equiv, i'.equiv]) (isCrys_prod PD h h')



variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

end GlobalTheory.Cmp.WachMonoidal
end
end

