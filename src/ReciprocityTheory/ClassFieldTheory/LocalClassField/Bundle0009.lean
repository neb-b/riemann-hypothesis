module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0007
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0005
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0002
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0008

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfResEqZeroOfCoprime
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open ReciprocityTheory.Coh Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

abbrev resP (M : TRep R G) (U : Subgroup G) : Pair M (M.resSub U) :=
  Pair.res M U.subtype continuous_subtype_val

theorem pair_H_bijective {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : IsHomeomorph P.φ)
    (hu : IsHomeomorph P.u) (n : ℕ) : Bijective (P.hom.H n) :=
  Deg2.pair_bij P hφ hu n

theorem infRes2_exact (M : TRep R G) (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (Q : TRep R (G ⧸ N)) (P : Pair Q M) (hP : IsInvRep M N Q P) (h1 : Subsingleton ((M.resSub N).H 1)) :
    Exact (P.hom.H 2) ((resP M N).hom.H 2) :=
  Deg2.exact2 M N Q P hN hP h1

theorem exists_normal_index_eq_prime {H : Type*} [Group H] [Finite H] [Nontrivial H] (l : ℕ) [Fact l.Prime]
    (hH : IsPGroup l H) : ∃ N : Subgroup H, N.Normal ∧ N.index = l :=
  Deg2.exists_normal_index l hH

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.Kummer
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

namespace Kummer

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

theorem exists_primitive_unit : ∃ ζ : (PadicAlgCl p)ˣ, IsPrimitiveRoot ζ n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) n
  exact ⟨_, hζ.isUnit_unit (NeZero.ne n)⟩

theorem isEmbedding_muMap {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Topology.IsEmbedding (muMap ζ hζ.pow_eq_one) :=
  (Continuous.isClosedEmbedding continuous_of_discreteTopology (muMap_injective hζ)).isEmbedding

theorem contAction_muRep : ReciprocityTheory.Gal.ContAction (muRep p K n) := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit p n
  show Continuous fun q : GK p K × ZMod n => muRep p K n q.1 q.2
  rw [(isEmbedding_muMap p n hζ).continuous_iff]
  have h : (muMap ζ hζ.pow_eq_one ∘ fun q : GK p K × ZMod n => muRep p K n q.1 q.2) =
      fun q => kbarRep p K q.1 (muMap ζ hζ.pow_eq_one q.2) := funext fun q => muMap_equiv K ζ _ q.1 q.2
  rw [h]
  exact (contAction_kbarRep p K).comp (f := fun q : GK p K × ZMod n => (q.1, muMap ζ hζ.pow_eq_one q.2))
    (continuous_fst.prodMk (continuous_of_discreteTopology.comp continuous_snd))

def muT : TRep ℤ (GK p K) where
  V := ZMod n
  rho := muRep p K n
  cont := contAction_muRep p K n


variable {p n} in
def iP {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : Pair (muT p K n) (kT p K) :=
  Pair.ofMap (M := muT p K n) (M' := kT p K) (muMap ζ hζ.pow_eq_one)
    (continuous_of_discreteTopology : Continuous (muMap ζ hζ.pow_eq_one : ZMod n → KbarMult p))
    (muMap_equiv K ζ _)

def pP : Pair (kT p K) (kT p K) :=
  Pair.ofMap (M := kT p K) (M' := kT p K) (powMap p n)
    (continuous_of_discreteTopology : Continuous (powMap p n : KbarMult p → KbarMult p))
    fun g m => (map_zsmul (kbarRep p K g) (n : ℤ) m).symm

variable {p n} in
theorem adm {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : admitted (iP K hζ) (pP p K n) :=
  ⟨rfl, rfl, isEmbedding_muMap p n hζ, exact_muMap_powMap hζ,
    ⟨Function.surjInv (powMap_surjective (p := p) (n := n)),
      (continuous_of_discreteTopology : Continuous (Function.surjInv (powMap_surjective (p := p) (n := n)))),
      Function.surjInv_eq _⟩⟩

def unitsToInvariants' : Additive Kˣ →+ ReciprocityTheory.Gal.H0 (kT p K).rho where
  toFun a := ⟨(Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul) : KbarMult p),
    fun σ => Units.ext (σ.commutes _)⟩
  map_zero' := Subtype.ext (by simp; rfl)
  map_add' a b := Subtype.ext (by simp; rfl)

theorem units_to_invariants_prime_injective : Function.Injective (unitsToInvariants' p K) := by
  intro a b hab
  have h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul =
      Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul := congrArg Subtype.val hab
  exact Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1

theorem units_to_invariants_prime_surjective : Function.Surjective (unitsToInvariants' p K) := by
  rintro ⟨x, hx⟩
  have : IsGalois K (PadicAlgCl p) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have h1 : ∀ σ : GK p K, σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = (Additive.toMul x : (PadicAlgCl p)ˣ) :=
    fun σ => congrArg (fun y : KbarMult p => ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)) (hx σ)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero ha.symm
  exact ⟨Additive.ofMul (Units.mk0 a ha0), Subtype.ext (Units.ext ha)⟩

theorem power_map_h0_unitsToInvariants (b : Kˣ) :
    (pP p K n).h0 (unitsToInvariants' p K (Additive.ofMul b)) = unitsToInvariants' p K (Additive.ofMul (b ^ n)) := by
  refine Subtype.ext ?_
  show powMap p n (Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b) : KbarMult p) = _
  rw [powMap_apply, ← map_pow]
  rfl

end

end Kummer

open Kummer

theorem h1_roots_of_unity_equiv_of_h1_subsingleton (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]
    (h90 : Subsingleton (H1 (kbarRep p K))) :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit p n
  obtain ⟨δ₀, δ₁, -, -, -, -, e2, e3, -⟩ :=
    low_degree_long_exact_sequence ℤ (GK p K) (muT p K n) (kT p K) (kT p K) (iP K hζ) (pP p K n) (adm K hζ)
  have h90' : Subsingleton (ReciprocityTheory.Gal.H1 (kT p K).rho) := h90
  have hs : Function.Surjective δ₀ := fun y => (e3 y).1 (Subsingleton.elim _ _)
  let ψ : Kˣ →* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    AddMonoidHom.toMultiplicativeRight (δ₀.toAddMonoidHom.comp (unitsToInvariants' p K))
  have hψ : ∀ a : Kˣ, ψ a = Multiplicative.ofAdd (δ₀ (unitsToInvariants' p K (Additive.ofMul a))) := fun a => rfl
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hs y.toAdd
    obtain ⟨a, rfl⟩ := units_to_invariants_prime_surjective p K x
    exact ⟨a.toMul, hx⟩
  have hker : ψ.ker = (powMonoidHom n : Kˣ →* Kˣ).range := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro ha
      have ha' : δ₀ (unitsToInvariants' p K (Additive.ofMul a)) = 0 := ha
      obtain ⟨y, hy⟩ := (e2 _).1 ha'
      obtain ⟨b, rfl⟩ := units_to_invariants_prime_surjective p K y
      refine ⟨b.toMul, ?_⟩
      have := (power_map_h0_unitsToInvariants p K n b.toMul).symm.trans hy
      exact units_to_invariants_prime_injective p K this
    · rintro ⟨b, rfl⟩
      show δ₀ (unitsToInvariants' p K (Additive.ofMul (b ^ n))) = 0
      exact (e2 _).2 ⟨_, power_map_h0_unitsToInvariants p K n b⟩
  have E1 : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  exact ⟨(h1ScalarEquiv (charRep (cycK p K n)) (muRep p K n) fun _ _ => rfl).trans (MulEquiv.toAdditiveLeft E1).symm⟩

theorem h1_roots_of_unity_equiv_units_quot_pow (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n] :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) :=
  h1_roots_of_unity_equiv_of_h1_subsingleton p K n (h1_kbarRep_subsingleton p K)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrand
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

noncomputable def uE (h : K ≤ L) [(subG p K L).Normal] :
    (layerU p K L).V →+ Additive (IntermediateField.extendScalars h)ˣ where
  toFun w := Additive.ofMul (Units.mk0 (⟨uval w, uval_mem h w⟩ : IntermediateField.extendScalars h)
    (fun h0 => uval_ne_zero w (congrArg Subtype.val h0)))
  map_zero' := Units.ext (Subtype.ext rfl)
  map_add' _ _ := Units.ext (Subtype.ext rfl)

theorem finiteIndex_of_ball (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal]
    (X : AddSubgroup (layerU p K L).V) {ε : ℝ} (hε : 0 < ε) (hX : ∀ w, ‖uval w - 1‖ < ε → w ∈ X) :
    X.FiniteIndex := by
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  have hc : IsCompact (Metric.closedBall (0 : L) 1) := isCompact_closedBall 0 1
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hc (e := ε) hε
  have hex : ∀ w : (layerU p K L).V, ∃ y : t, ‖uval w - ((y : L) : PadicAlgCl p)‖ < ε := by
    intro w
    have hw : (⟨uval w, uval_mem h w⟩ : L) ∈ Metric.closedBall (0 : L) 1 := by
      rw [mem_closedBall_zero_iff]; exact (norm_uval w).le
    obtain ⟨y, hy, hwy⟩ := Set.mem_iUnion₂.1 (hcov hw)
    rw [Metric.mem_ball, dist_eq_norm] at hwy
    exact ⟨⟨y, hy⟩, hwy⟩
  choose c hc' using hex
  have hsub : ∀ w w', c w = c w' → w - w' ∈ X := by
    intro w w' hww
    apply hX
    have h1 : uval (w - w') - 1 = (uval w - uval w') * (uval w')⁻¹ := by
      rw [uval_sub, sub_mul, mul_inv_cancel₀ (uval_ne_zero w')]
    rw [h1, norm_mul, norm_inv, norm_uval, inv_one, mul_one]
    have h2 : uval w - uval w' = (uval w - ((c w : L) : PadicAlgCl p)) - (uval w' - ((c w : L) : PadicAlgCl p)) := by
      ring
    rw [h2, sub_eq_add_neg]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hc' w) ?_)
    rw [norm_neg, hww]; exact hc' w'
  have : Finite t := htf
  have hfin : Finite ((layerU p K L).V ⧸ X) := by
    refine Finite.of_injective (fun q => c q.out) fun q q' hqq => ?_
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
    have := hsub _ _ hqq.symm
    rwa [sub_eq_neg_add] at this
  exact AddSubgroup.finiteIndex_of_finite_quotient

theorem exists_layerU_sub (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] :
    ∃ W : Submodule ℤ (layerU p K L).V, (∀ g, ∀ w ∈ W, (layerU p K L).rho g w ∈ W) ∧
      W.toAddSubgroup.FiniteIndex ∧
      (∀ w ∈ W, (∀ g, (layerU p K L).rho g w = w) → ∃ w' ∈ W, ∑ g, (layerU p K L).rho g w' = w) ∧
      ∀ g₀ : GalLK p K L, (∀ g, g ∈ Subgroup.zpowers g₀) → ∀ w ∈ W, ∑ g, (layerU p K L).rho g w = 0 →
        ∃ w' ∈ W, (layerU p K L).rho g₀ w' - w' = w := by
  classical
  let E : IntermediateField K (PadicAlgCl p) := IntermediateField.extendScalars h
  have hfd : FiniteDimensional K E := by
    have : FiniteDimensional ℚ_[p] E := hL
    exact FiniteDimensional.right ℚ_[p] K _
  have hst : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L := (subG_normal_iff h).1 inferInstance
  have hnorm : Normal K E := by
    rw [IntermediateField.normal_iff_forall_map_le']
    rintro σ _ ⟨x, hx, rfl⟩
    exact hst σ x hx
  have hgal : IsGalois K E := ⟨⟩
  obtain ⟨S, hS1, hS2, ⟨ε, hε, hS3⟩, hS4, hS5⟩ := exists_units_subgroup_padic hK E
  let r : GK p K →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E
  have hr : ∀ (σ : GK p K) (x : E), ((r σ x : E) : PadicAlgCl p) = σ x := fun σ x =>
    AlgEquiv.restrictNormalHom_apply E σ x
  have hrs : Surjective r := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (PadicAlgCl p)
  have hker : ∀ σ : GK p K, r σ = 1 ↔ σ ∈ subG p K L := by
    intro σ
    constructor
    · intro h1 x hx
      have := hr σ ⟨x, hx⟩
      rw [h1] at this
      exact this.symm
    · intro hσ
      ext x
      rw [hr]
      exact hσ x.1 x.2
  let f : GalLK p K L →* (E ≃ₐ[K] E) := QuotientGroup.lift (subG p K L) r fun σ hσ => (hker σ).2 hσ
  have hf : ∀ σ : GK p K, f (QuotientGroup.mk σ) = r σ := fun σ => rfl
  have hfb : Bijective f := by
    refine ⟨(injective_iff_map_eq_one f).2 fun q hq => ?_, fun τ => ?_⟩
    · induction q using QuotientGroup.induction_on with
      | H σ => exact (QuotientGroup.eq_one_iff σ).2 ((hker σ).1 hq)
    · obtain ⟨σ, rfl⟩ := hrs τ
      exact ⟨QuotientGroup.mk σ, rfl⟩
  let e : GalLK p K L ≃* (E ≃ₐ[K] E) := MulEquiv.ofBijective f hfb
  let ι : (layerU p K L).V → Eˣ := fun w => Additive.toMul (uE h w)
  have hι : ∀ w, (((ι w : Eˣ) : E) : PadicAlgCl p) = uval w := fun w => rfl
  have hιrho : ∀ g w, ((ι ((layerU p K L).rho g w) : Eˣ) : E) = e g (ι w : E) := by
    intro g w
    induction g using QuotientGroup.induction_on with
    | H σ =>
      apply Subtype.ext
      rw [hι, uval_rho]
      exact (hr σ (ι w : E)).symm
  have hιsurj : ∀ v ∈ S, ∃ w, ι w = v := by
    intro v hv
    obtain ⟨w, hw⟩ := exists_uval (K := K) (L := L) (x := ((v : E) : PadicAlgCl p)) (v : E).2 (hS2 v hv)
    exact ⟨w, Units.ext (Subtype.ext hw)⟩
  have hprod : ∀ w, uval (∑ g, (layerU p K L).rho g w) = ((∏ τ : E ≃ₐ[K] E, τ (ι w : E) : E) : PadicAlgCl p) := by
    intro w
    rw [uval_sum, ← Fintype.prod_equiv e.toEquiv (fun g => e g (ι w : E)) (fun τ => τ (ι w : E)) (fun _ => rfl),
      IntermediateField.coe_prod]
    exact Finset.prod_congr rfl fun g _ => by rw [← hιrho, hι]
  let X : AddSubgroup (layerU p K L).V := (Subgroup.toAddSubgroup S).comap (uE h)
  have hX : ∀ w, w ∈ X ↔ ι w ∈ S := fun w => Iff.rfl
  refine ⟨AddSubgroup.toIntSubmodule X, fun g w hw => ?_, ?_, fun w hw hfix => ?_, fun g₀ hg₀ w hw hN => ?_⟩
  · exact hS1 (e g) (ι w) _ hw (hιrho g w)
  · rw [AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact finiteIndex_of_ball hL h X hε fun w hw => hS3 (ι w) hw
  · obtain ⟨v, hv, hvw⟩ := hS4 (ι w) hw fun τ => by
      obtain ⟨g, rfl⟩ := e.surjective τ
      rw [← hιrho, hfix]
    obtain ⟨w', rfl⟩ := hιsurj v hv
    refine ⟨w', hv, uval_injective ?_⟩
    rw [hprod, hvw, hι]
  · obtain ⟨v, hv, hvw⟩ := hS5 (e g₀) (fun τ => by
      obtain ⟨g, rfl⟩ := e.surjective τ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ g)
      rw [map_zpow]
      exact Subgroup.zpow_mem_zpowers _ _) (ι w) hw (by
        apply Subtype.ext
        rw [← hprod, hN]
        rfl)
    obtain ⟨w', rfl⟩ := hιsurj v hv
    refine ⟨w', hv, uval_injective ?_⟩
    rw [uval_sub, ← hι, hιrho, hvw, MulMemClass.coe_mul, hι, hι, mul_assoc, mul_inv_cancel₀ (uval_ne_zero w'),
      mul_one]

theorem herbrand_of_sub {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] (ρ : Representation ℤ G M) (g₀ : G)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (W : Submodule ℤ M) (hW1 : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hW2 : W.toAddSubgroup.FiniteIndex)
    (hW3 : ∀ w ∈ W, (∀ g, ρ g w = w) → ∃ w' ∈ W, ∑ g, ρ g w' = w)
    (hW4 : ∀ w ∈ W, ∑ g, ρ g w = 0 → ∃ w' ∈ W, ρ g₀ w' - w' = w) :
    Herbrand.HFin ρ g₀ ∧ Herbrand.h ρ g₀ = 1 := by
  let ρW : Representation ℤ G W :=
    { toFun := fun g => (ρ g).restrict (p := W) (q := W) (hW1 g)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show ρ 1 x.1 = x.1
        rw [map_one]; rfl)
      map_mul' := fun a b => LinearMap.ext fun x => Subtype.ext (by
        show ρ (a * b) x.1 = ρ a (ρ b x.1)
        rw [map_mul]; rfl) }
  have hρ : ∀ g (x : W), ((ρW g x : W) : M) = ρ g x.1 := fun _ _ => rfl
  have hsum : ∀ x : W, ((∑ g, ρW g x : W) : M) = ∑ g, ρ g x.1 := by
    intro x
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun g _ => hρ g x
  have h0 : Subsingleton (Herbrand.TateZerothCohomology ρW g₀) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with
    | H a =>
    induction b using QuotientAddGroup.induction_on with
    | H b =>
    rw [Herbrand.mk_eq_mk_iff]
    have hab : ((a : W) - (b : W)) ∈ (Herbrand.dHom ρW g₀).ker := (a - b).2
    rw [Herbrand.mem_ker_dHom_iff ρW g₀ hg] at hab
    obtain ⟨w', hw', hw⟩ := hW3 ((a : W) - (b : W) : W).1 ((a : W) - (b : W) : W).2
      (fun g => congrArg Subtype.val (hab g))
    refine ⟨⟨w', hw'⟩, ?_⟩
    rw [Herbrand.nHom_apply]
    exact Subtype.ext ((hsum _).trans hw)
  have h1 : Subsingleton (Herbrand.H1 ρW g₀) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with
    | H a =>
    induction b using QuotientAddGroup.induction_on with
    | H b =>
    rw [Herbrand.mk_eq_mk_iff]
    have hab : ((a : W) - (b : W)) ∈ (Herbrand.nHom ρW).ker := (a - b).2
    rw [AddMonoidHom.mem_ker, Herbrand.nHom_apply] at hab
    obtain ⟨w', hw', hw⟩ := hW4 ((a : W) - (b : W) : W).1 ((a : W) - (b : W) : W).2
      ((hsum _).symm.trans (congrArg Subtype.val hab))
    exact ⟨⟨w', hw'⟩, Subtype.ext hw⟩
  obtain ⟨hf, hh⟩ := Herbrand.h_of_subsingleton ρW g₀
  have hfi : (W.subtype.toAddMonoidHom).range.FiniteIndex := by
    have : (W.subtype.toAddMonoidHom).range = W.toAddSubgroup := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    rw [this]; exact hW2
  obtain ⟨hiff, heq⟩ := Herbrand.h_eq_of_finiteIndex ρW ρ g₀ W.subtype.toAddMonoidHom
    Subtype.val_injective hfi (fun _ _ => rfl)
  exact ⟨hiff.1 hf, (heq hf).symm.trans hh⟩

theorem herbrand_layerU (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Herbrand.HFin (layerU p K L).rho g₀ ∧ Herbrand.h (layerU p K L).rho g₀ = 1 := by
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := exists_layerU_sub hK hL h
  exact herbrand_of_sub (layerU p K L).rho g₀ hg W hW1 hW2 hW3 (hW4 g₀ hg)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsC
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem norm_le_norm_iff_vK_of_pos (he : 0 < eK p K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x := by
  have he' : (0 : ℝ) < eK p K := by positivity
  rw [← Real.logb_le_logb (one_lt_p_real p) (norm_units_pos x) (norm_units_pos y), ← Int.cast_le (R := ℝ),
    vK_spec, vK_spec, neg_le_neg_iff, mul_le_mul_iff_right₀ he']

theorem norm_le_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he x 1
  rw [vK_one] at h
  simpa using h

theorem norm_lt_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he 1 x
  rw [vK_one] at h
  have h' : (1 : ℝ) ≤ ‖((x : K) : PadicAlgCl p)‖ ↔ vK p K x ≤ 0 := by simpa using h
  rw [← not_le, h']
  omega

theorem mem_UK_iff_of_pos (he : 0 < eK p K) (x : Kˣ) : x ∈ UK p K ↔ vK p K x = 0 := by
  show ‖((x : K) : PadicAlgCl p)‖ = 1 ↔ _
  have h1 := norm_le_one_iff_vK_of_pos p K he x
  have h2 := norm_lt_one_iff_vK_of_pos p K he x
  constructor
  · intro h
    have h3 := h1.1 h.le
    have h4 : ¬ (1 ≤ vK p K x) := fun h5 => (h2.2 h5).ne h
    omega
  · intro h
    have h3 := h1.2 (by omega)
    have h4 : ¬ ‖((x : K) : PadicAlgCl p)‖ < 1 := fun h5 => by have := h2.1 h5; omega
    exact le_antisymm h3 (not_lt.1 h4)

theorem mem_UK_iff (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) : x ∈ UK p K ↔ vK p K x = 0 :=
  mem_UK_iff_of_pos p K (eK_pos p K hK) x

theorem norm_le_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := norm_le_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_lt_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := norm_lt_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_le_norm_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x :=
  norm_le_norm_iff_vK_of_pos p K (eK_pos p K hK) x y

theorem vK_p (x : Kˣ) (hx : ((x : K) : PadicAlgCl p) = (p : PadicAlgCl p)) : vK p K x = eK p K := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec, hx, logb_norm_p]
  simp

def eLK : ℕ := eK p L / eK p K

def fLK : ℕ := fK p L / fK p K

variable {K L}

theorem multOf_mono (h : K ≤ L) : multOf p K ≤ multOf p L := fun _ hx => h hx

theorem valueGroup_mono (h : K ≤ L) : valueGroup p K ≤ valueGroup p L := AddSubgroup.map_mono (multOf_mono p h)

theorem eK_dvd_of_le (h : K ≤ L) : eK p K ∣ eK p L :=
  ⟨_, (AddSubgroup.relIndex_mul_relIndex (AddSubgroup.zmultiples (1 : ℝ)) (valueGroup p K) (valueGroup p L)
    (AddSubgroup.zmultiples_le_of_mem (one_mem_valueGroup p K)) (valueGroup_mono p h)).symm⟩

theorem eK_eq_mul_of_le (h : K ≤ L) : eK p L = eLK p K L * eK p K := (Nat.div_mul_cancel (eK_dvd_of_le p h)).symm

theorem eK_eq_mul (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : eK p L = eLK p K L * eK p K := eK_eq_mul_of_le p h

theorem eK_eq_of_norm (h : K ≤ L) (hn : ∀ x ∈ L, ∃ y ∈ K, ‖x‖ = ‖y‖) : eK p L = eK p K := by
  have h1 : valueGroup p L = valueGroup p K := by
    refine le_antisymm ?_ (valueGroup_mono p h)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hn _ hx
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [norm_zero, norm_eq_zero] at hxy
      exact (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero hxy
    refine ⟨Additive.ofMul (Units.mk0 y hy0), hy, ?_⟩
    rw [vbar_apply p x, hxy]
    rfl
  unfold eK
  rw [h1]

theorem eK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : eK p (Kn p K n) = eK p K :=
  eK_eq_of_norm p (le_Kn p K n) fun _ hx => norm_Kn p K hK hn hx

theorem eLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : eLK p K (Kn p K n) = 1 := by
  rw [eLK, eK_Kn p hK hn, Nat.div_self (eK_pos p K hK)]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

