module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitMulPowOfKummerVanishesOnInertiaCurve
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularUnitsOfRootMemKummerAdjoin
section
open scoped MatrixGroups TensorProduct
open Polynomial

namespace GlobalTheory.KZ.UnRoot

theorem exists_comap_eq {K L : Type} [Field K] [Field L] (f : K →+* L) (U : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap f = U := by
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp U.subtype)
  have key : ∀ x ∈ U.nonunits, f x ∈ W.nonunits := by
    intro x hx
    obtain ⟨hxU, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hx
    refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2 ⟨hW ⟨x, hxU⟩, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
    exact fun hu => hm (hloc.map_nonunit ⟨x, hxU⟩ hu)
  refine ⟨W, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxU
    have h0 : x ≠ 0 := by rintro rfl; exact hxU U.zero_mem
    have h1 : x⁻¹ ∈ U.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff, map_inv₀]
      have : 1 < U.valuation x := by
        rw [← not_le, ValuationSubring.valuation_le_one_iff]; exact hxU
      exact inv_lt_one_of_one_lt₀ this
    have h2 := key _ h1
    rw [ValuationSubring.mem_nonunits_iff, map_inv₀, map_inv₀] at h2
    have h3 : W.valuation (f x) ≤ 1 := (W.valuation_le_one_iff _).2 hx
    have h4 : 0 < W.valuation (f x) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact (map_ne_zero f).2 h0
    exact absurd ((inv_lt_one₀ h4).1 h2) (not_lt.2 h3)
  · intro x hx
    exact hW ⟨x, hx⟩

theorem val_eq_one_iff {F : Type} [Field F] (T : ValuationSubring F) (y : F) :
    T.valuation y = 1 ↔ y ≠ 0 ∧ y ∈ T ∧ y⁻¹ ∈ T := by
  rw [← T.valuation_le_one_iff, ← T.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨fun h0 => ?_, h.le, by rw [h, inv_one]⟩
    rw [h0, map_zero] at h
    exact zero_ne_one h
  · rintro ⟨h0, h₁, h₂⟩
    have : 0 < T.valuation y := zero_lt_iff.2 ((_root_.map_ne_zero _).2 h0)
    exact le_antisymm h₁ ((inv_le_one₀ this).1 h₂)

theorem val_comap_eq_one {K K' : Type} [Field K] [Field K'] (f : K →+* K') (S : ValuationSubring K') (x : K) :
    (S.comap f).valuation x = 1 ↔ S.valuation (f x) = 1 := by
  rw [val_eq_one_iff, val_eq_one_iff, ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀,
    _root_.map_ne_zero]

theorem val_eq_one_of_pow {L : Type} [Field L] (A : ValuationSubring L) {x : L} {n : ℕ} (hn : n ≠ 0)
    (h : A.valuation (x ^ n) = 1) : A.valuation x = 1 := by
  rw [map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' h1 hn))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 hn))

theorem root_eq_one {F : Type} [Field F] (V : ValuationSubring F) {m : ℕ} (hm : V.valuation (m : F) = 1) {ζ : F}
    (hζ : ζ ^ m = 1) (hV : V.valuation (ζ - 1) < 1) : ζ = 1 := by
  first
  | exact @_root_.GlobalTheory.RootOfUnityEqOne.main
  | exact _root_.GlobalTheory.RootOfUnityEqOne.main
  | (apply _root_.GlobalTheory.RootOfUnityEqOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootOfUnityEqOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootOfUnityEqOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootOfUnityEqOne.main ..)

theorem fix_root {L : Type} [Field L] (B : ValuationSubring L) {m : ℕ} (hm0 : m ≠ 0) (hm : B.valuation (m : L) = 1)
    {y U g : L} (hy : y ^ m = U) (hg : g ≠ 0) (hu : B.valuation (U / g ^ m) = 1) (φ : L →+* L) (hU : φ U = U)
    (hφg : φ g = g) (hφ : ∀ x, B.valuation x ≤ 1 → B.valuation (φ x - x) < 1) : φ y = y := by
  have hz : B.valuation (y / g) = 1 := val_eq_one_of_pow B hm0 (by rw [div_pow, hy]; exact hu)
  have hz0 : y / g ≠ 0 := ((val_eq_one_iff B _).1 hz).1
  have hy0 : y ≠ 0 := fun h => hz0 (by rw [h, zero_div])
  have h1 : (φ y / y) ^ m = 1 := by
    rw [div_pow, ← map_pow, hy, hU, div_self]
    rw [← hy]; exact pow_ne_zero _ hy0
  have h2 := hφ _ hz.le
  have e : φ (y / g) - y / g = (φ y / y - 1) * (y / g) := by
    rw [map_div₀, hφg]; field_simp
  rw [e, map_mul, hz, mul_one] at h2
  have := root_eq_one B hm h1 h2
  exact (div_eq_one_iff_eq hy0).1 this

theorem fix_adjoin {K L : Type} [Field K] [Field L] [Algebra K L] (Q : (L →+* L) → Prop) (S : Set L)
    (hS : ∀ y ∈ S, ∃ T : Finset K, ∀ φ, Q φ → (∀ t ∈ T, φ (algebraMap K L t) = algebraMap K L t) → φ y = y)
    {θ : L} (hθ : θ ∈ IntermediateField.adjoin K S) :
    ∃ T : Finset K, ∀ φ, Q φ → (∀ t ∈ T, φ (algebraMap K L t) = algebraMap K L t) → φ θ = θ := by
  classical
  induction hθ using IntermediateField.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap x => exact ⟨{x}, fun φ _ h => h x (Finset.mem_singleton_self x)⟩
  | add x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := hx
    obtain ⟨T', hT'⟩ := hy
    exact ⟨T ∪ T', fun φ hq h => by
      rw [map_add (f := _), hT φ hq fun t ht => h t (Finset.mem_union_left _ ht),
        hT' φ hq fun t ht => h t (Finset.mem_union_right _ ht)]⟩
  | inv x _ hx =>
    obtain ⟨T, hT⟩ := hx
    exact ⟨T, fun φ hq h => by rw [map_inv₀, hT φ hq h]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := hx
    obtain ⟨T', hT'⟩ := hy
    exact ⟨T ∪ T', fun φ hq h => by
      rw [map_mul, hT φ hq fun t ht => h t (Finset.mem_union_left _ ht),
        hT' φ hq fun t ht => h t (Finset.mem_union_right _ ht)]⟩

theorem core {k K L : Type} [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (B : ValuationSubring L) (hB : ∀ p : k[X], algebraMap K L (algebraMap k[X] K p) ∈ B) {l : ℕ} (hl : 0 < l)
    (f : K) (hf : f ≠ 0) (θ : L) (hθ : θ ^ l = algebraMap K L f) (T : Finset K)
    (hT : ∀ φ : L →+* L, (∀ x, B.valuation x ≤ 1 → B.valuation (φ x - x) < 1) →
      (∀ t ∈ T, φ (algebraMap K L t) = algebraMap K L t) → φ θ = θ) :
    ∃ c : K, c ≠ 0 ∧ B.valuation (algebraMap K L (f / c ^ l)) = 1 := by
  classical
  let E : IntermediateField (RatFunc k) K := IntermediateField.adjoin (RatFunc k) ((insert f T : Finset K) : Set K)
  have hE : ∀ t ∈ insert f T, t ∈ E := fun t ht => IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 ht)
  haveI : FiniteDimensional (RatFunc k) E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic E K := inferInstance
  haveI : Module.IsTorsionFree E L := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E L := ⟨inferInstance, Algebra.IsAlgebraic.trans E K L⟩
  haveI : CharZero K := charZero_of_injective_ringHom (algebraMap (RatFunc k) K).injective
  haveI : CharZero L := charZero_of_injective_ringHom (algebraMap K L).injective
  haveI : NeZero (l : L) := ⟨Nat.cast_ne_zero.2 hl.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L l
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hl.ne'] at hθ
    exact hf ((map_eq_zero _).1 hθ.symm)
  obtain ⟨c, hc, hv⟩ := GlobalTheory.KumVal.exists_unit_of_kum_eq_zero k E L l ζ hl hζ ⟨f, hE f (Finset.mem_insert_self _ _)⟩ θ
    (fun h => hf (congrArg Subtype.val h)) hθ B (by
      intro x hx
      have hx' : IsIntegral k[X] x := hx
      obtain ⟨p, hp, hpx⟩ := hx'
      let ρ : k[X] →+* B := ((algebraMap K L).comp (algebraMap k[X] K)).codRestrict B hB
      have hi : IsIntegral B (algebraMap E L x) := by
        refine ⟨p.map ρ, hp.map ρ, ?_⟩
        rw [eval₂_map]
        have := congrArg (algebraMap E L) hpx
        rw [hom_eval₂, map_zero] at this
        exact this
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
      rw [← hy]; exact y.2)
    (fun g hg => GlobalTheory.NeedB.kum_eq_of hζ hθ0 0 (by
      have := hT (g : L →+* L) hg fun t ht => g.commutes ⟨t, hE t (Finset.mem_insert_of_mem ht)⟩
      simpa using this))
  refine ⟨c, fun h => hc (Subtype.ext h), ?_⟩
  exact hv

end GlobalTheory.KZ.UnRoot

open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.UnRoot

theorem mem_Un_of_root_mem_adjoin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (m l : ℕ), 0 < m → 0 < l → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), θ ∈ IntermediateField.adjoin X.K {y : AlgebraicClosure X.K | ∃ U ∈ X.Un m, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (U : X.K)} → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → f ∈ X.Un l := by
  intro Ω _ _ _ ε X m l hm hl θ f hθ hf W hW
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_ringHom (algebraMap ℚ Ω).injective
  obtain ⟨B, rfl⟩ := exists_comap_eq (algebraMap X.K (AlgebraicClosure X.K)) W
  let e := RatFunc.algEquivOfTranscendental X.jK (GlobalTheory.K4.jK_transcendental X)
  let ψ : RatFunc Ω →ₐ[Ω] X.K := (IntermediateField.val _).comp e.toAlgHom
  letI : Algebra (RatFunc Ω) X.K := ψ.toRingHom.toAlgebra
  letI : Algebra (Polynomial Ω) X.K := (ψ.toRingHom.comp (algebraMap (Polynomial Ω) (RatFunc Ω))).toAlgebra
  haveI : IsScalarTower (Polynomial Ω) (RatFunc Ω) X.K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic (RatFunc Ω) X.K := ⟨fun x => by
    refine (X.alg_j x).ringHom_of_comp_eq (e.symm : _ →+* RatFunc Ω) (RingHom.id _) e.symm.injective ?_
    ext a
    show ((e (e.symm a) : _) : X.K) = a
    rw [e.apply_symm_apply]⟩
  have hp : ∀ p : (Polynomial Ω), algebraMap (Polynomial Ω) X.K p ∈ B.comap (algebraMap X.K (AlgebraicClosure X.K)) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      have : algebraMap (Polynomial Ω) X.K (C a) = algebraMap Ω X.K a := by
        rw [← ψ.commutes a]; rfl
      rw [this]; exact hW.1 a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a h =>
      have : algebraMap (Polynomial Ω) X.K Polynomial.X = X.jK := by
        show ((e (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X) : _) : X.K) = _
        rw [RatFunc.algebraMap_X, RatFunc.algEquivOfTranscendental_X]
      rw [pow_succ, ← mul_assoc, map_mul, this]
      exact mul_mem h hW.2
  have hmB : B.valuation (m : AlgebraicClosure X.K) = 1 := by
    have h1 : (B.comap (algebraMap X.K (AlgebraicClosure X.K))).valuation (algebraMap Ω X.K (m : Ω)) = 1 := by
      rw [val_eq_one_iff, ← map_inv₀]
      exact ⟨(_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hm.ne'), hW.1 _, hW.1 _⟩
    rw [val_comap_eq_one] at h1
    simpa using h1
  obtain ⟨T, hT⟩ := fix_adjoin (fun φ => ∀ x, B.valuation x ≤ 1 → B.valuation (φ x - x) < 1) _ (by
    rintro y ⟨U, hU, hy⟩
    obtain ⟨g, hg⟩ := hU _ hW
    rw [val_comap_eq_one, map_div₀, map_pow] at hg
    exact ⟨{(U : X.K), (g : X.K)}, fun φ hq h => fix_root B hm.ne' hmB hy ((_root_.map_ne_zero _).2 g.ne_zero) hg φ
      (h _ (by simp)) (h _ (by simp)) hq⟩) hθ
  obtain ⟨c, hc, hv⟩ := core (k := Ω) B hp hl (f : X.K) f.ne_zero θ hf T hT
  exact ⟨Units.mk0 c hc, (val_comap_eq_one _ _ _).2 hv⟩

end GlobalTheory.KZ.UnRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TiedRecordExistsOfActionPin
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnTies

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure RunData (J : CoreJ D) : Type 1 where

  loc : In66 J.Q

  nab : ∀ j, NabV (J.Q.Xo j) J.Q.c

  dδ : ∀ j n, DeltaDat (J.Q.Xo j) J.Q.c n

  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ

  half₂ : Ideal (𝓞 D.host.E)

abbrev RunData.full {J : CoreJ D} (r : RunData J) : Full D :=
  ⟨⟨J.toCore, r.loc, r.nab, r.dδ⟩, J.cE, J.chiW, J.x₀, J.iota, r.xi, r.half₂⟩

section Cusp

variable (B : WeightFamilies.Prov D) {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [NumberField K] [Algebra B.KO K] {n : ℕ}

def supSpan (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) : Submodule (𝓞 K) (Fin n → K) := spanK z (B.Mlat j w : Set _)

def shortSpan {P6 : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.PJ D B P6 j) (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) :
    Submodule (𝓞 K) (Fin n → K) := spanK z (X.shortTh w : Set _)

def scaledSpan {P6 : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (wL wF : WeightFamilies.Wt D j) (nT : ℕ) (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) : Submodule (𝓞 K) (Fin n → K) :=
  spanK z {F | X.inc w F ∈ X.Theta (scalOfP B hinj EX p w wL wF nT) w wL wF nT}




omit [NumberField K] in
theorem exists_cuspRep_of_injective (f : B.Cusp j w →ₗ[B.KO] (Fin n → K)) (hf : Function.Injective f) {P : Type} [Group P]
    (σ : Representation K P (Fin n → K)) (a : P → B.Cusp j w → B.Cusp j w) (ha : ∀ g F, f (a g F) = σ g (f F)) :
    ∃ ρ : Representation B.KO P (B.Cusp j w), ∀ g F, ρ g F = a g F := by
  refine ⟨{ toFun := fun g =>
              { toFun := a g
                map_add' := fun F F' => hf (by rw [map_add (f := _), ha, ha, ha, map_add (f := _), map_add (f := _)])
                map_smul' := fun c F => hf ?_ }
            map_one' := LinearMap.ext fun F => hf ?_
            map_mul' := fun g g' => LinearMap.ext fun F => hf ?_ }, fun _ _ => rfl⟩
  · rw [RingHom.id_apply, map_smul, ha, ha, map_smul, LinearMap.map_smul_of_tower]
  · change f (a 1 F) = f F
    rw [ha, map_one, one_apply_eq_self]
  · change f (a (g * g') F) = f (a g (a g' F))
    rw [ha, ha, ha, map_mul, mul_apply_eq_comp]

end Cusp

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem ActionPin.exists_rep {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {i : Fin D.R.m}
    {ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)}
    (ha : ActionPin h fw i ℓ) {P : Type} [Group P] (inc : P →* G) :
    ∃ ρ : Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)),
      IsLevAct T.toTop h ((i : ℕ) + 1) (κ i) (fun g => ℓ (inc g)) fun g F => ρ g F := by
  obtain ⟨a, h1, h2⟩ := ha
  obtain ⟨ρ, hρ⟩ := exists_cuspRep_of_injective (recB h.toLawsCore) (cuspTo h fw i) (cutTo_spec fw i).1
    ((R.FW i).ρ.comp inc) (fun g => a (inc g)) fun g F => h2 (inc g) F
  exact ⟨ρ, fun g F => (congrArg Subtype.val (hρ g F)).trans (h1 (inc g) F)⟩

section Tied

variable (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData T.J) (hr : ∀ v, LawsP (r v).full.toTop)
  (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (ι : Bs.J → Fin D.R.m) (wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)) (nT : ℕ) (inc : P →* G)
  (ℓ : ∀ i, G → (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
  (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ)
  (ρ : ∀ i, Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))))
  (O : OnObj S P oc)
  (z : ∀ i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))


end Tied

def blankObj (D : D7) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst)
    (n : Bs.J → ℕ) : OnObj S P oc where
  nZ := n
  ρ _ := 1
  U := ⊥
  ψ := 1
  V₀ _ := ⊥
  e _ := 0
  Ms _ := ⊥
  φ _ := 0
  Th1 _ _ := ⊥
  Th _ _ := ⊥
  ThK _ _ := ⊥
  Th0 _ _ := ⊥
  ThJ _ _ := ⊥
  X₃ _ _ := ⊥
  σ := 0
  a := 0
  E := 0
  r1 := 0
  r2 := 0
  pde := D.host.pde
  ε0 := 0
  nX := 0
  θ' _ _ := 0
  eX _ _ := 0
  pr _ _ := 0
  Mt _ _ := ⊥
  nnK := 0
  Jp := 0
  k := D.R.k
  m := D.R.m
  f := D.R.f
  bp := 0
  Sc := 0
  eta := 0
  T := 0
  DF := 0
  X2 := 0
  x := 0
  eps := 0
  vd := 0
  rr := D.R.r
  de2 := 0
  Nc := 0
  wt := 0
  th := 0
  ad := 0
  T2 := D.host.T2.card
  g1 := D.host.g 0
  g2 := D.host.g 1
  q1 := D.host.q
  dd := D.host.d
  sm := D.host.small

section Exists

variable (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData T.J) (hr : ∀ v, LawsP (r v).full.toTop)
  (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst)
  (ι : Bs.J → Fin D.R.m) (wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)) (nT : ℕ) (inc : P →* G)

end Exists

end GlobalTheory.OnTies
end
end

