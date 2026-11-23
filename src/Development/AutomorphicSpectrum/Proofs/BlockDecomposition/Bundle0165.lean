module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0161
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0107
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimePowAnnihilatorReduction
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfAlg

theorem pow_mul_mem_span_iff {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (n m : ℕ) (x : R) :
    a ^ n * x ∈ Ideal.span {a ^ (n + m)} ↔ x ∈ Ideal.span {a ^ m} := by
  have hn : a ^ n ∈ nonZeroDivisors R := pow_mem ha n
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
    have e : a ^ n * (c * a ^ m) = a ^ n * x := by rw [← hc, pow_add]; ring
    exact sub_eq_zero.1 (mem_nonZeroDivisors_iff_left.1 hn (c * a ^ m - x) (by rw [mul_sub, e, sub_self]))
  · intro h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
    exact Ideal.mem_span_singleton'.2 ⟨c, by rw [pow_add]; ring⟩

theorem lseq : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n m : ℕ), Function.Surjective (A.red (Nat.le_add_right n m)) ∧ (∀ x : A.Acr (n + m), A.red (Nat.le_add_right n m) x = 0 ↔ x ∈ Ideal.span {(l : A.Acr (n + m)) ^ n}) ∧ (∀ x : A.Acr (n + m), (l : A.Acr (n + m)) ^ n * x = 0 ↔ A.red (Nat.le_add_left m n) x = 0) ∧ ∀ x : A.U, (l : A.U) ^ n * x ∈ Ideal.span {(l : A.U) ^ (n + m)} ↔ x ∈ Ideal.span {(l : A.U) ^ m} := by
  intro l _ A n m
  have hl : (l : A.Acr0) ∈ nonZeroDivisors A.Acr0 := A.acris_torsion_free l (Fact.out : l.Prime).ne_zero
  have mk0 : ∀ (k : ℕ) (y : A.Acr0), A.mkAcr k y = 0 ↔ y ∈ Ideal.span {(l : A.Acr0) ^ k} :=
    fun k y => Ideal.Quotient.eq_zero_iff_mem
  refine ⟨?_, ?_, ?_, fun x => pow_mul_mem_span_iff (_root_.GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular A).1 n m x⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨A.mkAcr _ y, rfl⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.red _ (A.mkAcr _ y) = 0 ↔ A.mkAcr _ y ∈ _
    rw [red_mk, mk0]
    constructor
    · intro h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      refine Ideal.mem_span_singleton'.2 ⟨A.mkAcr _ c, ?_⟩
      rw [map_mul, map_pow, map_natCast]
    · intro h
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective c
      have e : A.mkAcr (n + m) (d * (l : A.Acr0) ^ n - y) = 0 := by
        set_option synthInstance.maxHeartbeats 400000 in
          rw [map_sub, map_mul, map_pow, map_natCast]
        exact sub_eq_zero.2 hc
      have e2 := (mk0 _ _).1 e
      have e3 : Ideal.span {(l : A.Acr0) ^ (n + m)} ≤ Ideal.span {(l : A.Acr0) ^ n} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_add_right n m))
      have e4 := Ideal.sub_mem _ (Ideal.mul_mem_left _ d (Ideal.mem_span_singleton_self ((l : A.Acr0) ^ n))) (e3 e2)
      rwa [sub_sub_cancel] at e4
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change _ * A.mkAcr _ y = 0 ↔ A.red _ (A.mkAcr _ y) = 0
    rw [red_mk, mk0, ← pow_mul_mem_span_iff hl n m y, ← mk0, map_mul, map_pow, map_natCast]

end GlobalTheory.CompanionTheory.PerfAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Pull1RestrictPairRestriction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.SysBC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} {P : Type} [SemilatticeInf P]

theorem exists_sec_equiv (h : IsPullback φ s' s (spMap (algebraMap R R'))) {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ e : R' ⊗[R] Sec s U ≃ₗ[R'] Sec s' (φ ⁻¹ᵁ U),
      ∀ b, e (1 ⊗ₜ b) = (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom b := by
  letI : Algebra (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI : Algebra R (Sec s' (φ ⁻¹ᵁ U)) :=
    ((algebraMap R' (Sec s' (φ ⁻¹ᵁ U))).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' (φ ⁻¹ᵁ U)) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (GlobalTheory.AbLaw.appLE_cst h.w le_rfl r).symm
  haveI hp : Algebra.IsPushout R R' (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp (GlobalTheory.AbLaw.isPushout_cst h hU rfl)
  refine ⟨hp.out.equiv, fun b ↦ ?_⟩
  exact (hp.out.equiv_tmul 1 b).trans (one_smul _ _)

def pullSys (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) : Sys X' P where
  u a := ⟨φ ⁻¹ᵁ (S.u a).1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h (S.u a).2⟩
  map_inf a b := by
    change φ ⁻¹ᵁ (S.u (a ⊓ b)).1 = φ ⁻¹ᵁ (S.u a).1 ⊓ φ ⁻¹ᵁ (S.u b).1
    rw [S.map_inf]; rfl
  cover := by
    change ⨆ a, φ ⁻¹ᵁ (S.u a).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, S.cover]; rfl

def pt (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) (a : P) : Pair φ :=
  ⟨((pullSys h S).u a, S.u a), le_rfl⟩

theorem pt_mono (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    Monotone (pt h S) := fun _ _ hab ↦
  Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(pullSys h S).mono hab, S.mono hab⟩)

def ptFn (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) : Pᵒᵖ ⥤ (Pair φ)ᵒᵖ :=
  (pt_mono h S).functor.op

def ptRes (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    CoefMap (RingHom.id R') (OPair φ s') (OSys s' (pullSys h S)) where
  G := ptFn h S
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def pullBC (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    BC (OSys s S) (OSys s' (pullSys h S)) where
  α T := secPull s s' (pt h S T.unop)
  naturality ψ b := (pairPull h.w).naturality ((ptFn h S).map ψ) b
  smul T r b := (pairPull h.w).smul (op (pt h S T.unop)) r b
  bij T := exists_sec_equiv h (S.u T.unop).2

theorem pull1_restrict_pair_pullback (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P)
    (c : HO1 s) : (ptRes h S).pull1 ((pairPull h.w).pull1 c) =
      (pullBC h S).coef.pull1 ((resSys s S).pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

theorem pull1_restrict_pair_restriction (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P)
    (c : HO1 s') : (ptRes h S).pull1 ((pairRes φ s').pull1 c) =
      (resSys s' (pullSys h S)).pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

end GlobalTheory.CompanionTheory.SysBC


open GlobalTheory.CompanionTheory.SysBC in
theorem GlobalTheory.CompanionTheory.SysBC.sysBCSt : DescentSt → LowSt → SysBCSt := by
  intro hD hL R R' _ _ _ X X' s s' φ h hs P _ S
  have hs' : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) h hs
  refine ⟨pullSys h S, pullBC h S, fun c c' e ↦ ?_⟩
  have inj := (hL R' _ _ _ _ (resSys s' (pullSys h S)) (hD R' X' s' hs' P (pullSys h S))).1.1
  obtain ⟨x, hx⟩ := (pairRes_bijective φ s').1.2 ((pairPull h.w).pull1 c)
  have e' : x = c' := inj (by
    rw [← pull1_restrict_pair_restriction h S x, hx, pull1_restrict_pair_pullback, e])
  exact hx.symm.trans (congrArg _ e')
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfUpwardClosedCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CosieveRel

theorem serre_of_equiv {R : Type} [CommRing R] (𝒮 : Serre.{1} R) {M N : Type 1} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : 𝒮.P M) : 𝒮.P N := by
  refine 𝒮.mid M N PUnit.{2} e.toLinearMap 0 ?_ h (𝒮.zero PUnit.{2} inferInstance)
  intro y
  exact iff_of_true (Subsingleton.elim _ _) ⟨e.symm y, e.apply_symm_apply y⟩

theorem serre_union : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (W : ι → ObjectProperty C) (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') (𝒮 : Serre.{1} R) (n : ℕ),
    (∀ p q, p + q = n → 𝒮.P ((CrystallineSemistableComparison.Pb.cechH F W q).cx.H p)) → 𝒮.P (HU F (fun T => ∃ α, W α T) n) := by
  intro R _ C _ F ι W hW 𝒮 n h
  have hle : ∀ α, W α ≤ (fun T => ∃ β, W β T : ObjectProperty C) := fun α T hT => ⟨α, hT⟩
  refine _root_.GlobalTheory.CompanionTheory.CechSerre.serre_cech ((ObjectProperty.ι (fun T => ∃ β, W β T : ObjectProperty C)) ⋙ F)
    (fun α T => W α T.obj) (fun α => by
      intro T T' f hT
      exact hW α f.hom hT T'.property) (fun T => T.property) 𝒮 n ?_
  intro p q hpq
  obtain ⟨e⟩ := _root_.GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H F (fun T => ∃ β, W β T : ObjectProperty C) W hle q p
  exact serre_of_equiv 𝒮 e.symm (h p q hpq)

end GlobalTheory.CompanionTheory.CosieveRel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransfer
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w' w₁ w₂ w₃ w₄ w₅ t₁ t₂ t₃ t₄ t₅

section Alg

theorem five_add {A₁ : Type w₁} {A₂ : Type w₂} {A₃ : Type w₃} {A₄ : Type w₄} {A₅ : Type w₅}
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅]
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : A₁ →+ A₂) (u₂ : A₂ →+ A₃) (u₃ : A₃ →+ A₄) (u₄ : A₄ →+ A₅)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (g₁ : A₁ →+ L₁) (g₂ : A₂ →+ L₂) (g₃ : A₃ →+ L₃) (g₄ : A₄ →+ L₄) (g₅ : A₅ →+ L₅)
    (c₁ : ∀ x, g₂ (u₁ x) = v₁ (g₁ x)) (c₂ : ∀ x, g₃ (u₂ x) = v₂ (g₂ x))
    (c₃ : ∀ x, g₄ (u₃ x) = v₃ (g₃ x)) (c₄ : ∀ x, g₅ (u₄ x) = v₄ (g₄ x))
    (eA₂ : Function.Exact u₁ u₂) (eA₃ : Function.Exact u₂ u₃) (eA₄ : Function.Exact u₃ u₄)
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (s₁ : Function.Surjective g₁) (b₂ : Function.Bijective g₂) (b₄ : Function.Bijective g₄)
    (i₅ : Function.Injective g₅) : Function.Bijective g₃ := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : u₃ x = 0 := b₄.1 (by rw [c₃, hx, map_zero, map_zero])
    obtain ⟨y, rfl⟩ := (eA₃ x).1 h1
    have h2 : v₂ (g₂ y) = 0 := by rw [← c₂, hx]
    obtain ⟨z, hz⟩ := (eL₂ _).1 h2
    obtain ⟨t, rfl⟩ := s₁ z
    have h3 : u₁ t = y := b₂.1 (by rw [c₁, hz])
    exact (eA₂ _).2 ⟨t, h3⟩
  · intro t
    obtain ⟨p, hp⟩ := b₄.2 (v₃ t)
    have h1 : u₄ p = 0 := i₅ (by
      rw [c₄, hp, map_zero]
      exact (eL₄ _).2 ⟨t, rfl⟩)
    obtain ⟨q, rfl⟩ := (eA₄ p).1 h1
    have h2 : v₃ (t - g₃ q) = 0 := by rw [map_sub, ← c₃, hp, sub_self]
    obtain ⟨y', hy'⟩ := (eL₃ _).1 h2
    obtain ⟨y, rfl⟩ := b₂.2 y'
    refine ⟨q + u₂ y, ?_⟩
    rw [map_add (f := _), c₂, hy']
    abel

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_ext {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]
    (g h : (∀ i, N i ⊗[R] M i) →+ P) (H : ∀ i n x, g (Pi.single i (n ⊗ₜ x)) = h (Pi.single i (n ⊗ₜ x))) : g = h := by
  refine AddMonoidHom.functions_ext _ g h fun i t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x => exact H i n x
  | add x y hx hy => rw [Pi.single_add, map_add (f := _), map_add (f := _), hx, hy]

def piT {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) :
    (∀ i, N i ⊗[R] M i) →+ (∀ i, N i ⊗[R] M' i) where
  toFun t i := (u i).lTensor (N i) (t i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem piT_single {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) (i : ι) (n : N i) (x : M i) :
    piT (N := N) u (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ u i x) := by
  funext k
  by_cases h : k = i
  · subst h
    simp [piT]
  · simp [piT, Pi.single_eq_of_ne h]

theorem piT_exact [∀ i, Module.Flat R (N i)] {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] (u : ∀ i, M₁ i →ₗ[R] M₂ i) (v : ∀ i, M₂ i →ₗ[R] M₃ i)
    (h : ∀ i, Function.Exact (u i) (v i)) : Function.Exact (piT (N := N) u) (piT (N := N) v) := by
  intro t
  constructor
  · intro ht
    have h1 : ∀ i, ∃ s, (u i).lTensor (N i) s = t i := fun i =>
      (Module.Flat.lTensor_exact (N i) (h i) (t i)).1 (congrFun ht i)
    choose s hs using h1
    exact ⟨s, funext hs⟩
  · rintro ⟨s, rfl⟩
    funext i
    exact (Module.Flat.lTensor_exact (N i) (h i) _).2 ⟨s i, rfl⟩

theorem tens_zero {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {M' : Type w'} [AddCommGroup M']
    (hM : ∀ i, Subsingleton (M i)) (hM' : Subsingleton M') (f : ∀ i, N i → M i → M') :
    Tens R (N := N) (M := M) (M' := M') f := by
  have h0 : ∀ i, Subsingleton (N i ⊗[R] M i) := fun i => by
    refine ⟨fun x y => ?_⟩
    have : ∀ z : N i ⊗[R] M i, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [this x, this y]
  refine ⟨⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩, fun _ _ => by simp⟩,
    fun i n x => Subsingleton.elim _ _⟩

theorem tens_transfer {M : ι → Type w₁} {L : ι → Type w₂} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)] {M' : Type t₁} {L' : Type t₂} [AddCommGroup M'] [AddCommGroup L']
    (u : ∀ i, M i ≃ₗ[R] L i) (u' : M' ≃+ L') (f : ∀ i, N i → M i → M') (h : ∀ i, N i → L i → L')
    (hc : ∀ i n x, h i n (u i x) = u' (f i n x))
    (hf : Tens R (N := N) (M := M) (M' := M') f) : Tens R (N := N) (M := L) (M' := L') h := by
  obtain ⟨g, hg⟩ := hf
  let e : (∀ i, N i ⊗[R] L i) ≃+ (∀ i, N i ⊗[R] M i) :=
    { toFun := piT (N := N) fun i => ((u i).symm : L i →ₗ[R] M i)
      invFun := piT (N := N) fun i => ((u i) : M i →ₗ[R] L i)
      left_inv := fun t => by
        funext i
        change (((u i) : M i →ₗ[R] L i).lTensor (N i)) ((((u i).symm : L i →ₗ[R] M i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      right_inv := fun t => by
        funext i
        change (((u i).symm : L i →ₗ[R] M i).lTensor (N i)) ((((u i) : M i →ₗ[R] L i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      map_add' := map_add _ }
  refine ⟨(e.trans g).trans u', fun i n x => ?_⟩
  obtain ⟨y, rfl⟩ := (u i).surjective x
  have : e (Pi.single i (n ⊗ₜ u i y)) = Pi.single i (n ⊗ₜ y) := by
    change piT (N := N) (fun i => ((u i).symm : L i →ₗ[R] M i)) _ = _
    rw [piT_single]
    simp
  simp only [AddEquiv.trans_apply, this, hg, hc]

theorem tens_five [∀ i, Module.Flat R (N i)]
    {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃} {M₄ : ι → Type w₄} {M₅ : ι → Type w₅}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] [∀ i, AddCommGroup (M₄ i)] [∀ i, Module R (M₄ i)]
    [∀ i, AddCommGroup (M₅ i)] [∀ i, Module R (M₅ i)]
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : ∀ i, M₁ i →ₗ[R] M₂ i) (u₂ : ∀ i, M₂ i →ₗ[R] M₃ i) (u₃ : ∀ i, M₃ i →ₗ[R] M₄ i) (u₄ : ∀ i, M₄ i →ₗ[R] M₅ i)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (f₁ : ∀ i, N i → M₁ i → L₁) (f₂ : ∀ i, N i → M₂ i → L₂) (f₃ : ∀ i, N i → M₃ i → L₃)
    (f₄ : ∀ i, N i → M₄ i → L₄) (f₅ : ∀ i, N i → M₅ i → L₅)
    (c₁ : ∀ i n x, f₂ i n (u₁ i x) = v₁ (f₁ i n x)) (c₂ : ∀ i n x, f₃ i n (u₂ i x) = v₂ (f₂ i n x))
    (c₃ : ∀ i n x, f₄ i n (u₃ i x) = v₃ (f₃ i n x)) (c₄ : ∀ i n x, f₅ i n (u₄ i x) = v₄ (f₄ i n x))
    (eM₂ : ∀ i, Function.Exact (u₁ i) (u₂ i)) (eM₃ : ∀ i, Function.Exact (u₂ i) (u₃ i))
    (eM₄ : ∀ i, Function.Exact (u₃ i) (u₄ i))
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (h₁ : Tens R (N := N) (M := M₁) (M' := L₁) f₁) (h₂ : Tens R (N := N) (M := M₂) (M' := L₂) f₂)
    (h₄ : Tens R (N := N) (M := M₄) (M' := L₄) f₄) (h₅ : Tens R (N := N) (M := M₅) (M' := L₅) f₅)
    (hadd : ∀ i, ∃ F : N i ⊗[R] M₃ i →+ L₃, ∀ n x, F (n ⊗ₜ x) = f₃ i n x) :
    Tens R (N := N) (M := M₃) (M' := L₃) f₃ := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  obtain ⟨g₄, hg₄⟩ := h₄
  obtain ⟨g₅, hg₅⟩ := h₅
  choose F hF using hadd
  let g₃ : (∀ i, N i ⊗[R] M₃ i) →+ L₃ := ∑ i, (F i).comp (Pi.evalAddMonoidHom _ i)
  have hg₃ : ∀ i n x, g₃ (Pi.single i (n ⊗ₜ x)) = f₃ i n x := by
    intro i n x
    simp only [g₃, AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
    rw [Finset.sum_eq_single i]
    · simp [hF]
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  have b := five_add (piT (N := N) u₁) (piT (N := N) u₂) (piT (N := N) u₃) (piT (N := N) u₄) v₁ v₂ v₃ v₄
    g₁.toAddMonoidHom g₂.toAddMonoidHom g₃ g₄.toAddMonoidHom g₅.toAddMonoidHom
    (fun x => DFunLike.congr_fun (tens_ext (g₂.toAddMonoidHom.comp (piT (N := N) u₁)) (v₁.comp g₁.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₁, hg₂, c₁]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₃.comp (piT (N := N) u₂)) (v₂.comp g₂.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₂, hg₃, c₂]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₄.toAddMonoidHom.comp (piT (N := N) u₃)) (v₃.comp g₃)
      fun i n x => by simp [piT_single, hg₃, hg₄, c₃]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₅.toAddMonoidHom.comp (piT (N := N) u₄)) (v₄.comp g₄.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₄, hg₅, c₄]) x)
    (piT_exact u₁ u₂ eM₂) (piT_exact u₂ u₃ eM₃) (piT_exact u₃ u₄ eM₄) eL₂ eL₃ eL₄
    g₁.surjective g₂.bijective g₄.bijective g₅.injective
  exact ⟨AddEquiv.ofBijective g₃ b, hg₃⟩

end Alg

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TiltSequenceDeterminedBySharp
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem tilt_inj {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : ℕ → A.A)
    (ha : ∀ i, a (i + 1) ^ l = a i) (hb : ∀ i, b (i + 1) ^ l = b i)
    (hs : ∀ i, A.sharp (a i) = A.sharp (b i)) : a = b := by
  have hf : ∀ x y : A.A, (x - y) ^ l = x ^ l - y ^ l := fun x y => map_sub A.frob x y
  have key : ∀ j i, a i - b i = (a (i + j) - b (i + j)) ^ (l ^ j) := by
    intro j
    induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      rw [ih i, pow_succ' l j, pow_mul, hf, ← add_assoc, ha, hb]
  have hmem : ∀ j, a j - b j ∈ Ideal.span {A.pi} := by
    intro j
    rw [← (GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A).2, RingHom.mem_ker, map_sub, A.sharpMap_eq, A.sharpMap_eq,
      hs j, sub_self]
  have hdvd : ∀ i j, A.pi ^ j ∣ a i - b i := by
    intro i j
    have h1 : A.pi ∣ a (i + j) - b (i + j) := Ideal.mem_span_singleton.1 (hmem (i + j))
    rw [key j i]
    exact (pow_dvd_pow _ (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans (pow_dvd_pow_of_dvd h1 _)
  have hH : IsHausdorff (Ideal.span {A.pi}) A.A := A.compl.toIsHausdorff
  funext i
  refine sub_eq_zero.1 (hH.haus _ fun n => ?_)
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_span_singleton.2 (hdvd i n)

end GlobalTheory.CompanionTheory.Untilt
end

