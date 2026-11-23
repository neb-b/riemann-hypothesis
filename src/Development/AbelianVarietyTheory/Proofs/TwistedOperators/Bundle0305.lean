module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section

namespace GlobalTheory.GelfandLine

variable {G : Type} [Group G]

theorem mem_fixed_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

def stabSub (K : Subgroup G) (g : G) : Subgroup G where
  carrier := {h | h ∈ K ∧ g⁻¹ * h * g ∈ K}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K.mul_mem ha hb, ?_⟩
    convert K.mul_mem ha' hb' using 1
    group
  one_mem' := ⟨K.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨K.inv_mem ha, ?_⟩
    convert K.inv_mem ha' using 1
    group

theorem mem_stabSub {K : Subgroup G} {g h : G} : h ∈ stabSub K g ↔ h ∈ K ∧ g⁻¹ * h * g ∈ K := Iff.rfl

def heckeOp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (g : G)
    [Fintype (K ⧸ (stabSub K g).subgroupOf K)] : Module.End ℂ V :=
  ∑ q : K ⧸ (stabSub K g).subgroupOf K, ρ ((q.out : G) * g)

theorem heckeOp_apply {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] (v : V) :
    heckeOp ρ K g v = ∑ q : K ⧸ (stabSub K g).subgroupOf K, ρ ((q.out : G) * g) v := by
  simp [heckeOp, LinearMap.sum_apply]

def repSet (K : Subgroup G) (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] : Finset G :=
  Finset.univ.map ⟨fun q : K ⧸ (stabSub K g).subgroupOf K => (q.out : G) * g, fun q q' e => by
    have : (q.out : G) = q'.out := mul_right_cancel e
    exact Quotient.out_inj.1 (Subtype.ext this)⟩

theorem heckeOp_eq_sum {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] (v : V) :
    heckeOp ρ K g v = ∑ γ ∈ repSet K g, ρ γ v := by
  rw [heckeOp_apply, repSet, Finset.sum_map]
  rfl

theorem repSet_spec (K : Subgroup G) (a : G) [Fintype (K ⧸ (stabSub K a).subgroupOf K)] :
    (∀ γ ∈ repSet K a, GelfandTrick.InDoubleCoset K a γ) ∧
    (∀ x : G, GelfandTrick.InDoubleCoset K a x → ∃! γ, γ ∈ repSet K a ∧ γ⁻¹ * x ∈ K) := by
  constructor
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hγ
    refine ⟨q.out, q.out.2, 1, K.one_mem, ?_⟩
    show (q.out : G) * a = (q.out : G) * a * 1
    simp
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) (⟨k₁, hk₁⟩ : K)
    have hh' : ((h : K) : G) ∈ stabSub K a := Subgroup.mem_subgroupOf.1 h.2
    set q : K ⧸ (stabSub K a).subgroupOf K := ((⟨k₁, hk₁⟩ : K) : K ⧸ (stabSub K a).subgroupOf K)
    have hq : ((q.out : K) : G) = k₁ * ((h : K) : G) := by
      rw [hh]; rfl
    refine ⟨(q.out : G) * a, ⟨Finset.mem_map.2 ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · rw [hq]
      have : a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K := (mem_stabSub.1 (inv_mem hh')).2
      convert K.mul_mem this hk₂ using 1
      group
    · rintro y ⟨hy, hyx⟩
      obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hy
      change (p.out : G) * a = (q.out : G) * a
      congr 1
      have hx1 : ((q.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K := by
        rw [hq]
        have : a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K := (mem_stabSub.1 (inv_mem hh')).2
        convert K.mul_mem this hk₂ using 1
        group
      have hx2 : ((p.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K := hyx
      have hu : ((p.out : K)⁻¹ * q.out : K) ∈ (stabSub K a).subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        refine ⟨(p.out⁻¹ * q.out : K).2, ?_⟩
        convert K.mul_mem hx2 (K.inv_mem hx1) using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have : (p.out : K ⧸ (stabSub K a).subgroupOf K) = q.out := QuotientGroup.eq.2 hu
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      rw [this]

theorem sum_comm_anti {V : Type} [AddCommGroup V] (K : Subgroup G) (τ : G → G)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (hK : ∀ k ∈ K, τ k ∈ K)
    (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, GelfandTrick.InDoubleCoset K α γ)
    (hR' : ∀ x : G, GelfandTrick.InDoubleCoset K α x → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K)
    (hS : ∀ γ ∈ S, GelfandTrick.InDoubleCoset K β γ)
    (hS' : ∀ x : G, GelfandTrick.InDoubleCoset K β x → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ K)
    (F : G → V) (hF : ∀ k ∈ K, ∀ g, F (g * k) = F g) :
    ∑ γ ∈ R, ∑ δ ∈ S, F (γ * δ) = ∑ δ ∈ S, ∑ γ ∈ R, F (δ * γ) := by
  classical
  let f : G ⧸ K → V := fun c => F c.out
  have hf : ∀ g : G, f (g : G ⧸ K) = F g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [f, hk, hF k k.2]
  have key : ∀ A B : Finset G, ∑ γ ∈ A, ∑ δ ∈ B, F (γ * δ)
      = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ K) := fun A B => by
    rw [Finset.sum_product]
    simp only [hf]
  rw [key, key]
  let T : Finset (G ⧸ K) := (R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ K)) ∪
    (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ K))
  rw [← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ K))
      (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f,
    ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ K))
      (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  congr 1
  apply le_antisymm
  · convert GelfandTrick.card_pairs_le K τ hmul hinv hdc hK α β R S hR hR' hS hS' c
  · convert GelfandTrick.card_pairs_le K τ hmul hinv hdc hK β α S R hS hS' hR hR' c

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem heckeOp_comm (ρ : Representation ℂ G V) (K : Subgroup G) (τ : G → G)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (a b : G)
    [Fintype (K ⧸ (stabSub K a).subgroupOf K)] [Fintype (K ⧸ (stabSub K b).subgroupOf K)]
    {v : V} (hv : ∀ k ∈ K, ρ k v = v) :
    heckeOp ρ K a (heckeOp ρ K b v) = heckeOp ρ K b (heckeOp ρ K a v) := by
  have hK : ∀ k ∈ K, τ k ∈ K := fun k hk => by
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hdc k
    rw [e]; exact K.mul_mem (K.mul_mem h₁ hk) h₂
  have := sum_comm_anti K τ hmul hinv hdc hK a b _ _ (repSet_spec K a).1 (repSet_spec K a).2
    (repSet_spec K b).1 (repSet_spec K b).2 (fun g => ρ g v)
    (fun k hk g => by simp only [map_mul, Module.End.mul_apply, hv k hk])
  rw [heckeOp_eq_sum ρ K a (heckeOp ρ K b v), heckeOp_eq_sum ρ K b v,
    heckeOp_eq_sum ρ K b (heckeOp ρ K a v), heckeOp_eq_sum ρ K a v]
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_mul, Module.End.mul_apply] using this

theorem heckeTerm_eq (ρ : Representation ℂ G V) (K : Subgroup G) (a : G) {v : V}
    (hv : ∀ k ∈ K, ρ k v = v) (y : K) :
    ρ ((((y : K ⧸ (stabSub K a).subgroupOf K)).out : G) * a) v = ρ ((y : G) * a) v := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) y
  have hh' : ((h : K) : G) ∈ stabSub K a := Subgroup.mem_subgroupOf.1 h.2
  rw [hh]
  have e : ((y * (h : K) : K) : G) * a = (y : G) * a * (a⁻¹ * ((h : K) : G) * a) := by
    simp only [Subgroup.coe_mul]; group
  rw [e, map_mul, Module.End.mul_apply, hv _ hh'.2]

theorem heckeOp_fixed (ρ : Representation ℂ G V) (K : Subgroup G) (a : G)
    [Fintype (K ⧸ (stabSub K a).subgroupOf K)] {v : V} (hv : ∀ k ∈ K, ρ k v = v) :
    ∀ k ∈ K, ρ k (heckeOp ρ K a v) = heckeOp ρ K a v := by
  intro k hk
  set_option synthInstance.maxHeartbeats 100000 in
    rw [heckeOp_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  have hq : (MulAction.toPerm (⟨k, hk⟩ : K) q : K ⧸ (stabSub K a).subgroupOf K) =
      ((⟨k, hk⟩ * q.out : K) : K ⧸ (stabSub K a).subgroupOf K) := by
    show (⟨k, hk⟩ : K) • q = _
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hq, heckeTerm_eq ρ K a hv, ← Module.End.mul_apply, ← map_mul, ← mul_assoc]
  rfl

theorem finsum_quot_le {K W : Type} [Group K] [AddCommGroup W] {H H' : Subgroup K} (hle : H ≤ H')
    [H.FiniteIndex] (F : K → W) (hF : ∀ y, ∀ h ∈ H', F (y * h) = F y) :
    ∑ᶠ q : K ⧸ H, F q.out = Nat.card (H' ⧸ H.subgroupOf H') • ∑ᶠ p : K ⧸ H', F p.out := by
  classical
  haveI : H'.FiniteIndex := Subgroup.finiteIndex_of_le hle
  let e := Subgroup.quotientEquivProdOfLE hle
  haveI : Finite ((K ⧸ H') × (H' ⧸ H.subgroupOf H')) := Finite.of_equiv _ e
  haveI : Finite (H' ⧸ H.subgroupOf H') := Finite.prod_right (K ⧸ H')
  haveI := Fintype.ofFinite (K ⧸ H)
  haveI := Fintype.ofFinite (K ⧸ H')
  haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have h1 : ∀ q : K ⧸ H, F q.out = F (e q).1.out := by
    intro q
    have : (e q).1 = ((q.out : K) : K ⧸ H') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H' q.out
    rw [hh, hF _ _ h.2]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Fintype.sum_equiv e _ (fun y => F y.1.out) (fun _ => rfl),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [Finset.smul_sum]

end GlobalTheory.GelfandLine


open GlobalTheory.GelfandLine in
theorem GlobalTheory.fixed_eq_span_of_gelfandPair : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), ρ.IsIrreducible → IsAdmissible ρ → ∀ x ∈ fixed ρ K, x ≠ 0 → fixed ρ K = ℂ ∙ x := by
  first
  | exact @_root_.GlobalTheory.GroupAverageProjection.main
  | exact _root_.GlobalTheory.GroupAverageProjection.main
  | (apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GroupAverageProjection.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GroupAverageProjection.main ..)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfiniteHeightTransposeGramUnitaryLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.HtInfKapX

open GlobalTheory.AdelicU (htInf htOf normInf opNorm compInf)

theorem opNorm_reindex_le {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) ≤ opNorm y := by
  unfold GlobalTheory.AdelicU.opNorm
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  let c : EuclideanSpace ℂ m → EuclideanSpace ℂ n := fun z => WithLp.toLp 2 fun i => z (e i)
  let c' : EuclideanSpace ℂ n → EuclideanSpace ℂ m := fun z => WithLp.toLp 2 fun j => z (e.symm j)
  have hc : ∀ z, ‖c z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c]
    congr 1
    exact Equiv.sum_comp e (fun j => ‖z j‖₊ ^ 2)
  have hc' : ∀ z, ‖c' z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c']
    congr 1
    exact Equiv.sum_comp e.symm (fun j => ‖z j‖₊ ^ 2)
  have h : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) (reindex e e y) x =
      c' (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y (c x)) := by
    ext j
    change ∑ k, y (e.symm j) (e.symm k) * x k = ∑ i, y (e.symm j) i * x (e i)
    rw [← Equiv.sum_comp e]
    simp
  rw [h, hc', ← hc x]
  exact ContinuousLinearMap.le_opNNNorm _ _

theorem opNorm_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) = opNorm y := by
  refine le_antisymm (opNorm_reindex_le e y) ?_
  have h : reindex e.symm e.symm (reindex e e y) = y := by ext; simp
  calc opNorm y = opNorm (reindex e.symm e.symm (reindex e e y)) := by rw [h]
    _ ≤ opNorm (reindex e e y) := opNorm_reindex_le e.symm _

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (w : NumberField.InfinitePlace F)

theorem normInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n (w.Completion ⊗[F] E)) : normInf F w (reindex e e y) = normInf F w y := by
  unfold GlobalTheory.AdelicU.normInf
  congr 1
  funext τ
  rw [reindex_apply, ← Matrix.submatrix_map, ← reindex_apply, opNorm_reindex]

theorem htInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (g : (Matrix n n (w.Completion ⊗[F] E))ˣ) :
    htInf F w (Units.map (Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e).toMonoidHom g) =
      htInf F w g := by
  have key : ∀ y, normInf F w ((Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e) y) =
      normInf F w y := fun y => by rw [Matrix.reindexAlgEquiv_apply, normInf_reindex]
  show GlobalTheory.AdelicU.htOf (normInf F w) _ = GlobalTheory.AdelicU.htOf (normInf F w) _
  rw [GlobalTheory.AdelicU.htOf, GlobalTheory.AdelicU.htOf, ← map_inv, Units.coe_map, Units.coe_map]
  exact congrArg₂ _ rfl (congrArg₂ _ (key _) (key _))

theorem bc_reindex {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) (g : (Matrix n n A)ˣ) :
    Formalism.UG.bc φ (Units.map (Matrix.reindexAlgEquiv A A e).toMonoidHom g) =
      Units.map (Matrix.reindexAlgEquiv B B e).toMonoidHom (Formalism.UG.bc φ g) := by
  ext i j
  rfl

theorem htInf_kapX_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal, ∀ h : GA D X, ∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) ≤ C * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h := by
  intro D θ hθ X d e J hJ
  refine ⟨1, fun h => ?_⟩
  rw [one_mul]
  refine le_of_eq ?_
  have key : ∀ w, GlobalTheory.AdelicU.htInf D.host.F w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) =
      GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom X h)) :=
    fun w => by
      show GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc _
        (Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (Formalism.L2.Theta.matHom X h))) = _
      rw [bc_reindex, htInf_reindex]
  simp only [key]
  exact (Function.Bijective.prod_comp (GlobalTheory.CMTypePlaces.places_bijective D) _).symm.trans
    (Finset.prod_congr rfl fun τ _ => GlobalTheory.Grow.htInf_eq_infHt X hθ τ h)

end GlobalTheory.HtInfKapX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict

variable {D : D7}

def sgE (ε : Bool) : D.host.E := if ε then 1 else -1

def PublishedHyps (D : D7) {n d : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) : Prop :=
  IsCMExt D.host.F D.host.E D.sp.cm.sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ' ∧
    (∀ i j, D.sp.cm.sig (Xs.J j i) = Xs.J i j) ∧ Xs.J.det ≠ 0 ∧
    (∀ i j, D.sp.cm.sig (Ws.J j i) = -Ws.J i j) ∧ Ws.J.det ≠ 0 ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX n ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW d ∧
    IsHecke D.host.F D.host.E χX ∧ IsHecke D.host.F D.host.E χW ∧ Mo.IsWeil ψ' χX χW om ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Xs.J.map (τ w).1) (Xs.θ w)) ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • Ws.J.map (τ w).1) (Ws.θ w))

structure IsPairReading (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (ω : WRep M X)
    (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws) (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) : Prop where

  psi : ψ' = ψ

  JX : Xs.J = sgE (D := D) ε • M.gram

  JW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))

  cart : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
    Ws.θ w = (B.cart t).map conj

  good : Mo.IsGood ψ'

  transp : GlobalTheory.TripleRead.IsTransp ψ ε Mo om ω (Equiv.refl (Fin X.rank)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (sgE (D := D) ε) JX)
    (GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) JW)

def IsFockMap (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)
    {Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank} {Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws)
    (Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank)) : Prop :=
  ∃ (f₀ : WO (sgn ε M) X → ℂ) (r : (Fin M.rank × Fin X.rank → AF D.host.F) → ℂ),
    IsVacF ψ θ (frSgn ε A) B f₀ ∧ f₀ ≠ 0 ∧
    ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r ∧
      GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram (Equiv.refl (Fin X.rank))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r) = ptF ψ θ (frSgn ε A) B f₀ P

end GlobalTheory.RealDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SquareAgree

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

structure IsThetaSubG (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W)
    (N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop where

  le : N ≤ algD M ψ emb

  fin : ∀ (v : Pl (F := F)) (f : SInf F (Fin n × Fin d)) (φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ), f ∈ M.Pol ψ emb →
    (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) → φ v ∈ augAt om v → pure f φ ∈ N

  lie : ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb,
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ ∈ N

  cpt : ∀ k ∈ KInf σ X emb, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb, Acts (evI F) (om (k, 1)) f f₁ →
    ∀ φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ - pure f φ ∈ N

  stabFin : ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N

  stabLie : ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ algD M ψ emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

  stabCpt : ∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N

theorem IsDatum.fun_eq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (AE F E) → Z) (hc : Function.Surjective crd) {Φ : (Fin n × Fin d → AF F) → ℂ} {f f' : Z → ℂ}
    (h : IsDatum M ψ crd Φ f) (h' : IsDatum M ψ crd Φ f') : f = f' := by
  funext z
  obtain ⟨u, rfl⟩ := hc z
  rw [← h.2 u, ← h'.2 u]

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaSeriesModerateGrowth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedSeriesGrowth

theorem mixed_series_growth : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), (∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω p f)) 0) ∧ ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (g, h) f)) 0‖ₑ ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  intro D V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hμ
  obtain ⟨⟨θ, hθ⟩, -, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨A₁, d, hF⟩ := _root_.GlobalTheory.MixedTerm.mixed_terms_bound D V V' W r C C' B hs h1 h2 h3 ψ hω.std θ hθ μ 𝓨 hμ
  obtain ⟨A₂, hS⟩ := _root_.GlobalTheory.WeilWordGrowth.sup_words_growth D ψ V W χS χT ω hω θ hθ d
  refine ⟨A₁ + A₂, fun f hf => ?_⟩
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K, hK⟩ := hF U hU
  obtain ⟨c, hc⟩ := hS f hf
  refine ⟨max K 0 * max c 0, fun g h => ⟨fun y => _root_.GlobalTheory.ResHeisCont.continuous_res_heisO D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ f hf _, ?_⟩⟩
  have hH : 0 ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h :=
    mul_nonneg (GlobalTheory.Grow.height_pos V g).le (GlobalTheory.Grow.height_pos W h).le
  refine (hK g h (ω (g, h) f) (hω.om_pres _ f hf) (fun u hu h0 => ?_)).trans ?_
  · rw [← hω.om_heis g h u f hf, hl u hu h0]
  · refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left K 0) (pow_nonneg hH _)))
      ((hc g h).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left c 0)
        (pow_nonneg hH _))))).trans_eq ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right K 0) (pow_nonneg hH _)), pow_add]
    congr 1; ring

end GlobalTheory.MixedSeriesGrowth

end
end

