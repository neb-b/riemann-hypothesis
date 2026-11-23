module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.BoxIsot
section
open UpperTheory.V.Z.J.D
open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

private lemma box_tmul {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (a : G) (b : H) (w : W) (v : W') :
    box ρ τ (a, b) (w ⊗ₜ[ℂ] v) = ρ a w ⊗ₜ[ℂ] τ b v := by
  simp [box, Representation.tprod_apply]

private lemma isot_factor {G H W W' X Y : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [Nontrivial W] (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (κ : Representation ℂ (G × H) X) (κ' : Representation ℂ H Y) (f : W ⊗[ℂ] Y ≃ₗ[ℂ] X)
    (hf : Intw (box ρ κ') κ f.toLinearMap) (h2 : Isot (κ.comp (MonoidHom.inr G H)) τ) :
    Isot κ' τ := by
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff ℂ w0).1 hcon)
  let p : X →ₗ[ℂ] Y := (TensorProduct.lid ℂ Y).toLinearMap ∘ₗ
    (TensorProduct.map φ LinearMap.id) ∘ₗ f.symm.toLinearMap
  have hp1 : ∀ w y, p (f (w ⊗ₜ[ℂ] y)) = φ w • y := fun w y => by
    simp [p]
  have hp2 : ∀ (h : H) (x : X), p (κ (1, h) x) = κ' h (p x) := by
    intro h x
    obtain ⟨t, rfl⟩ := f.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul w y =>
      have := hf (1, h) (w ⊗ₜ[ℂ] y)
      simp only [LinearEquiv.coe_coe] at this
      rw [← this, box_tmul, hp1, hp1]
      simp
  unfold Isot
  set S : Submodule ℂ Y := ⨆ g : {g : W' →ₗ[ℂ] Y // Intw τ κ' g}, LinearMap.range g.1 with hS
  have hle : (⊤ : Submodule ℂ X) ≤ S.comap p := by
    refine le_trans h2 (iSup_le fun u => ?_)
    rintro _ ⟨a, rfl⟩
    have hu : Intw τ κ' (p ∘ₗ u.1) := fun h v => by
      have := u.2 h v
      simp only [LinearMap.comp_apply]
      rw [this]
      exact hp2 h (u.1 v)
    exact (le_iSup (fun g : {g : W' →ₗ[ℂ] Y // Intw τ κ' g} => LinearMap.range g.1) ⟨_, hu⟩)
      ⟨a, rfl⟩
  intro y _
  have hy : p (f (w0 ⊗ₜ[ℂ] ((φ w0)⁻¹ • y))) ∈ S := hle (Submodule.mem_top)
  rw [hp1, smul_smul, mul_inv_cancel₀ hφ, one_smul] at hy
  exact hy

private lemma isot_tensor {G H W W' X Y : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (κ : Representation ℂ (G × H) X) (κ' : Representation ℂ H Y) (f : W ⊗[ℂ] Y ≃ₗ[ℂ] X)
    (hf : Intw (box ρ κ') κ f.toLinearMap) (h : Isot κ' τ) : Isot κ (box ρ τ) := by
  unfold Isot
  set T : Submodule ℂ X :=
    ⨆ F : {F : W ⊗[ℂ] W' →ₗ[ℂ] X // Intw (box ρ τ) κ F}, LinearMap.range F.1 with hT
  have hF : ∀ g : W' →ₗ[ℂ] Y, Intw τ κ' g →
      Intw (box ρ τ) κ (f.toLinearMap ∘ₗ TensorProduct.map LinearMap.id g) := by
    intro g hg ab t
    obtain ⟨a, b⟩ := ab
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
    | tmul w v =>
      have := hf (a, b) (w ⊗ₜ[ℂ] g v)
      simp only [LinearEquiv.coe_coe] at this
      rw [box_tmul] at this
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe, box_tmul]
      rw [hg b v, this]
  have hw : ∀ (w : W) (y : Y), f (w ⊗ₜ[ℂ] y) ∈ T := by
    intro w y
    have hle : (⊤ : Submodule ℂ Y) ≤
        T.comap (f.toLinearMap ∘ₗ TensorProduct.mk ℂ W Y w) := by
      refine le_trans h (iSup_le fun g => ?_)
      rintro _ ⟨a, rfl⟩
      exact (le_iSup (fun F : {F : W ⊗[ℂ] W' →ₗ[ℂ] X // Intw (box ρ τ) κ F} =>
        LinearMap.range F.1) ⟨_, hF g.1 g.2⟩) ⟨w ⊗ₜ[ℂ] a, by simp⟩
    exact hle (Submodule.mem_top (x := y))
  intro x _
  obtain ⟨t, rfl⟩ := f.surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht =>
    rw [map_add (f := _)]
    exact T.add_mem (hs (Submodule.mem_top)) (ht (Submodule.mem_top))
  | tmul w y => exact hw w y

end UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.boxIsot :
    Step → BoxIsot := by
  intro hStep G H W W' _ _ _ _ _ _ ρ τ hρ _ X _ _ κ h1 h2
  obtain ⟨Y, _, _, κ', f, hf⟩ := hStep G H X W κ ρ hρ h1
  haveI : Nontrivial W := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    obtain ⟨s, t, hst⟩ := hρ.1.toNontrivial.exists_pair_ne
    exact hst (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  exact isot_tensor ρ τ κ κ' f hf (isot_factor ρ τ κ κ' f hf h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.CompsEx
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

theorem compsEx : CompsEx := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV σ hσ
  have hund : ∀ {A : ValuationSubring Ω} {w : Plc L}, IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 (Lp L))) :=
    fun hA y => hA (algebraMap (𝓞 (Lp L)) (𝓞 L) y)
  have hwv : ∀ v, (s.w v).under (𝓞 (Lp L)) = v := fun v =>
    HeightOneSpectrum.ext (Ideal.ext fun y => (hund (s.hw v) y).symm.trans (s.hA v y))
  have hsp : ∀ v ∈ s.S, IsSplitAt (s.w v) := fun v hv =>
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v hv) _ (hwv v)
  have hex : ∀ w : Plc L, IsSplitAt w → ∃ τ : SmIrr (GLw n w), Cp σ w τ := fun w hw => by
    obtain ⟨τ, -, h1, -⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ, hσ⟩ w hw
    exact ⟨τ, h1⟩
  have hl : ∀ v : V.frame.Vl, v.1 ∈ s.S := fun v => Or.inl v.2
  have hu : ∀ u : s.St, u.1 ∈ s.S := fun u => Or.inr (Or.inl u.2)
  have ho : s.v0 ∈ s.S := Or.inr (Or.inr rfl)
  choose f hf using fun v (hv : v ∈ s.S) => hex (s.w v) (hsp v hv)
  exact ⟨⟨fun v => f _ (hl v), fun u => f _ (hu u), f _ ho, fun v => hf _ (hl v), fun u => hf _ (hu u), hf _ ho⟩⟩

end UpperTheory.V.Z.J.D
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DualDual
section
open NumberField GlobalTheory.UnitaryBC GlobalTheory.CuspRep Formalism.BasicNotions
open UpperTheory.V.Z.J.D

private theorem dual_dual' {n : ℕ} (lam : DomWeight n) : lam.dual.dual = lam := by
  have h : ∀ a b : DomWeight n, (∀ i, a.w i = b.w i) → a = b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    have : a = b := funext h
    subst this
    rfl
  exact h _ _ fun i => by simp [DomWeight.dual]

private theorem conj_wt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {σ : Submodule ℂ (UA E n → ℂ)}
    (hσ : IsAutRepU σ) {τ : E →+* ℂ} {μ : DomWeight n} (h : HasWeightAt σ τ μ) :
    HasWeightAt σ (ComplexEmbedding.conjugate τ) μ.dual :=
  (GlobalTheory.DefU.AU.hasWt_mk (⟨σ, hσ⟩ : GlobalTheory.DefU.AutSub E n) _ _).1
    ((GlobalTheory.DefU.AU.hasWt_mk (⟨σ, hσ⟩ : GlobalTheory.DefU.AutSub E n) _ _).2 h).conjugate

private theorem link_abs {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {I : Type} (φ : I → E →+* ℂ)
    (hb : Function.Bijective fun i => InfinitePlace.mk (φ i)) (μ : I → DomWeight n) :
    ∃ lam' : InfinitePlace E → DomWeight n, ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
      ((∀ i, HasWeightAt σ (φ i) (μ i)) ↔ ∀ v : InfinitePlace E, HasWeightAt σ v.embedding (lam' v)) := by
  classical
  choose y hy using hb.2
  have hconj : ∀ v, v.embedding ≠ φ (y v) → ComplexEmbedding.conjugate (φ (y v)) = v.embedding := fun v c => by
    have e : InfinitePlace.mk (φ (y v)) = InfinitePlace.mk v.embedding := (hy v).trans (InfinitePlace.mk_embedding v).symm
    exact (InfinitePlace.mk_eq_iff.1 e).resolve_left fun e' => c e'.symm
  refine ⟨fun v => if v.embedding = φ (y v) then μ (y v) else (μ (y v)).dual, fun σ hσ => ⟨fun h v => ?_, fun h i => ?_⟩⟩
  · by_cases c : v.embedding = φ (y v)
    · simp only [if_pos c]
      rw [c]
      exact h _
    · simp only [if_neg c]
      rw [← hconj v c]
      exact conj_wt hσ (h _)
  · have hi : y (InfinitePlace.mk (φ i)) = i := hb.1 (hy _)
    have key : ∀ v, HasWeightAt σ v.embedding (if v.embedding = φ (y v) then μ (y v) else (μ (y v)).dual) →
        HasWeightAt σ (φ (y v)) (μ (y v)) := fun v hv => by
      by_cases c : v.embedding = φ (y v)
      · simp only [if_pos c] at hv
        rwa [c] at hv
      · simp only [if_neg c] at hv
        have h2 := conj_wt hσ hv
        rw [← hconj v c, dual_dual'] at h2
        exact (star_star (φ (y v))) ▸ h2
    have h3 := key _ (h (InfinitePlace.mk (φ i)))
    rwa [hi] at h3

theorem UpperTheory.V.Z.J.D.wtEx :
    WtEx := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V _ ι lam
  exact link_abs (fun y : UpperTheory.V.Hi.Emb l (fun v : V.frame.Vl => s.w v.1) => ι.toRingHom.comp y.res)
    (UpperTheory.placeEmbeddings_bijective_infinitePlaces l L Ω s V ι).2 fun y => (lam y.res).dual
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.EigBox
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

section Lin

variable {W W₂ Z Z₂ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W₂] [Module ℂ W₂]
  [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z₂] [Module ℂ Z₂]

private def sl (l : Z →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] W :=
  (TensorProduct.rid ℂ W).toLinearMap ∘ₗ LinearMap.lTensor W l

private def sr (l : W →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] Z :=
  (TensorProduct.lid ℂ Z).toLinearMap ∘ₗ LinearMap.rTensor Z l

private theorem sl_tmul (l : Z →ₗ[ℂ] ℂ) (w : W) (z : Z) : sl l (w ⊗ₜ[ℂ] z) = l z • w := by
  simp [sl]

private theorem sr_tmul (l : W →ₗ[ℂ] ℂ) (w : W) (z : Z) : sr l (w ⊗ₜ[ℂ] z) = l w • z := by
  simp [sr]

end Lin

section Rep

variable {G Y X : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]

end Rep

section Main

variable {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V] {S : V → UpperTheory.V.W.Plc L}

end Main

section Inv

variable {G H : Type} [Group G] [Group H] {m : ℕ} (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ)

end Inv

section Box

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Box

end UpperTheory.V.Z.J.D
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.EquivOfChar
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace UpperTheory.V.Z.J.D

section Abs

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

private def mulMap (P K : Subgroup G) (hK : IsOpen (K : Set G)) (σ σ' : Representation ℂ P W) (c : G → ℂˣ)
    (hl : ∀ (p : P) (x : G) (v : W), ((c ((p : G) * x) : ℂˣ) : ℂ) • σ p v = σ' p (((c x : ℂˣ) : ℂ) • v))
    (hr : ∀ κ ∈ K, ∀ x, c (x * κ) = c x) : smoothPart (ind P σ) →ₗ[ℂ] smoothPart (ind P σ') where
  toFun f := ⟨⟨fun x => ((c x : ℂˣ) : ℂ) • f.1.1 x, fun p x => by
      have h := f.1.2 p x
      show ((c ((p : G) * x) : ℂˣ) : ℂ) • f.1.1 ((p : G) * x) = _
      rw [h]
      exact hl p x _⟩, by
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (Filter.inter_mem (f.2.mem_nhds (by simp)) (hK.mem_nhds K.one_mem)) ?_)
      rintro g ⟨h1, h2⟩
      have h3 : ind P σ g f.1 = f.1 := h1
      refine Subtype.ext (funext fun x => ?_)
      have h4 : f.1.1 (x * g) = f.1.1 x := congrArg (fun φ : indSpace P σ => φ.1 x) h3
      show ((c (x * g) : ℂˣ) : ℂ) • f.1.1 (x * g) = ((c x : ℂˣ) : ℂ) • f.1.1 x
      rw [h4, hr g h2]⟩
  map_add' f f' := Subtype.ext (Subtype.ext (funext fun x => smul_add _ (f.1.1 x) (f'.1.1 x)))
  map_smul' a f := Subtype.ext (Subtype.ext (funext fun x => smul_comm _ a (f.1.1 x)))

private theorem equiv_of_char (P K : Subgroup G) (hK : IsOpen (K : Set G))
    (hPK : ∀ x : G, ∃ p : P, ∃ w ∈ K, x = (p : G) * w) (σ σ' : Representation ℂ P W) (R : P →* ℂˣ)
    (hR : ∀ p : P, (p : G) ∈ K → R p = 1) (hσ : ∀ (p : P) (v : W), σ' p v = ((R p : ℂˣ) : ℂ) • σ p v) :
    Nonempty (Representation.Equiv ((smInd P σ).comp K.subtype) ((smInd P σ').comp K.subtype)) := by
  obtain ⟨c, hc⟩ : ∃ c : G → ℂˣ, ∀ (p : P) (w : G), w ∈ K → c ((p : G) * w) = R p := by
    refine ⟨fun x => R (Classical.choose (hPK x)), fun p w hw => ?_⟩
    obtain ⟨w', hw', hx⟩ := Classical.choose_spec (hPK ((p : G) * w))
    set q := Classical.choose (hPK ((p : G) * w))
    have hqp : ((q⁻¹ * p : P) : G) ∈ K := by
      have : ((q⁻¹ * p : P) : G) = w' * w⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hx, mul_inv_cancel_right]
      rw [this]
      exact K.mul_mem hw' (K.inv_mem hw)
    have := hR _ hqp
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  have hr : ∀ κ ∈ K, ∀ x, c (x * κ) = c x := by
    intro κ hκ x
    obtain ⟨p, w, hw, rfl⟩ := hPK x
    rw [mul_assoc, hc _ _ (K.mul_mem hw hκ), hc _ _ hw]
  have hmul : ∀ (p : P) (x : G), c ((p : G) * x) = R p * c x := by
    intro p x
    obtain ⟨q, w, hw, rfl⟩ := hPK x
    rw [← mul_assoc, ← Subgroup.coe_mul, hc _ _ hw, hc _ _ hw, map_mul]
  have hl : ∀ (p : P) (x : G) (v : W), ((c ((p : G) * x) : ℂˣ) : ℂ) • σ p v = σ' p (((c x : ℂˣ) : ℂ) • v) := by
    intro p x v
    rw [hσ, map_smul, smul_smul, hmul, Units.val_mul]
  have hl' : ∀ (p : P) (x : G) (v : W),
      ((((fun y => (c y)⁻¹) ((p : G) * x)) : ℂˣ) : ℂ) • σ' p v = σ p ((((fun y => (c y)⁻¹) x : ℂˣ) : ℂ) • v) := by
    intro p x v
    simp only [hσ, map_smul, smul_smul, hmul, ← Units.val_mul]
    congr 2
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hr' : ∀ κ ∈ K, ∀ x, (fun y => (c y)⁻¹) (x * κ) = (fun y => (c y)⁻¹) x := by
    intro κ hκ x
    simp only [hr κ hκ x]
  refine ⟨{ toFun := mulMap P K hK σ σ' c hl hr
            map_add' := (mulMap P K hK σ σ' c hl hr).map_add
            map_smul' := (mulMap P K hK σ σ' c hl hr).map_smul
            isIntertwining' := ?_
            invFun := mulMap P K hK σ' σ (fun y => (c y)⁻¹) hl' hr'
            left_inv := ?_
            right_inv := ?_ }⟩
  · intro g
    refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ((c x : ℂˣ) : ℂ) • f.1.1 (x * g) = ((c (x * g) : ℂˣ) : ℂ) • f.1.1 (x * g)
    rw [hr g g.2]
  · intro f
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show (((c x)⁻¹ : ℂˣ) : ℂ) • (((c x : ℂˣ) : ℂ) • f.1.1 x) = f.1.1 x
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  · intro f
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ((c x : ℂˣ) : ℂ) • ((((c x)⁻¹ : ℂˣ) : ℂ) • f.1.1 x) = f.1.1 x
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end Abs

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem exists_pw (x : GL (Fin n) k) :
    ∃ p : parab k (points (Fin n)), ∃ w ∈ KO k (Fin n), x = (p : GL (Fin n) k) * w := by
  obtain ⟨u, g, w, hw, hx⟩ := UnitInd.exists_iwasawa (points (Fin n)) x
  refine ⟨⟨(u : GL (Fin n) k) * leviEmb k (points (Fin n)) g,
    mul_mem (unipRad_le_parab k (points (Fin n)) u.2) (leviEmb_mem_parab k (points (Fin n)) g)⟩, w, hw, hx⟩

open GlobalTheory.SmGL.PrinProd in
private theorem dg_mem_Uo (p : parab k (points (Fin n))) (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (i : Fin n) :
    dg p i ∈ UpperTheory.V.Hi.Uo k := by
  have h1 := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hp).1 i i
  have h2 := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hp).2 i i
  rw [← PrinProd.val_dg] at h1
  have h3 : ((dg p⁻¹ i : kˣ) : k) ∈ 𝒪[k] := by
    rw [PrinProd.val_dg]
    simpa using h2
  rw [map_inv, Pi.inv_apply, Units.val_inv_eq_inv_val] at h3
  change valuation k _ = 1
  have a1 : valuation k ((dg p i : kˣ) : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 h1
  have a2 : valuation k ((dg p i : kˣ) : k)⁻¹ ≤ 1 := (Valuation.mem_integer_iff _ _).1 h3
  rw [map_inv₀] at a2
  have hne : valuation k ((dg p i : kˣ) : k) ≠ 0 := by simp
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 a2)

open GlobalTheory.SmGL.PrinProd in
private theorem sB_apply (χ : Fin n → kˣ →* ℂˣ) (p : parab k (points (Fin n))) (v : ℂ) :
    sB χ p v = ((deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) : ℂˣ) : ℂ) *
      (((torusChar χ (dg p) : ℂˣ) : ℂ) * v) := rfl

end Loc


open GlobalTheory.SmGL.PrinProd in
theorem psRes : PsRes := by
  intro k _ _ _ _ n ω ω' _ _ h
  let χ : Fin n → kˣ →* ℂˣ := fun i => ω i * absPow k ((↑n - 1) / 2)
  let χ' : Fin n → kˣ →* ℂˣ := fun i => ω' i * absPow k ((↑n - 1) / 2)
  let ρ : Fin n → kˣ →* ℂˣ := fun i => ω' i * (ω i)⁻¹
  have hχ : ∀ t, torusChar χ' t = torusChar ρ t * torusChar χ t := by
    intro t
    simp only [torusChar_apply, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [χ, χ', ρ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    group
  refine equiv_of_char (parab k (points (Fin n))) (KO k (Fin n)) GlobalTheory.SplitFlip.isOpen_KO exists_pw
    (sB χ) (sB χ') ((torusChar ρ).comp dg) (fun p hp => ?_) (fun p v => ?_)
  · rw [MonoidHom.comp_apply, torusChar_apply]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [ρ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [← h i ⟨_, dg_mem_Uo p hp i⟩, mul_inv_cancel]
  · rw [sB_apply, sB_apply, smul_eq_mul, MonoidHom.comp_apply, hχ, Units.val_mul]
    ring

end UpperTheory.V.Z.J.D
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.RankInvTBox
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

section Abs

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Abs

section Fam

variable {I : Type} {Gi Wi Wi' : I → Type} {H X X' : Type} [∀ i, Group (Gi i)] [Group H]
  [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] [∀ i, AddCommGroup (Wi' i)] [∀ i, Module ℂ (Wi' i)]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']

private theorem congr_piRep (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (τ' : ∀ i, Representation ℂ (Gi i) (Wi' i))
    (a : ∀ i, Wi i ≃ₗ[ℂ] Wi' i) (g : ∀ i, Gi i) (h : ∀ i x, a i (τ i (g i) x) = τ' i (g i) (a i x))
    (x : ⨂[ℂ] i, Wi i) : PiTensorProduct.congr a (piRep τ g x) = piRep τ' g (PiTensorProduct.congr a x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [piRep, PiTensorProduct.congr, map_smul, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, LinearEquiv.ofLinear_apply, PiTensorProduct.map_tprod]
    exact congrArg (fun t => r • PiTensorProduct.tprod ℂ t) (funext fun i => h i (f i))
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Fam

end UpperTheory.V.Z.J.D
end
end

