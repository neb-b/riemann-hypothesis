module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicDetCharacterFunctionConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

section Lin
variable {n k : Type} [Fintype n] [DecidableEq n] [CommRing k]

theorem gl_mulVec_inv_mulVec (X : GL n k) (v : n → k) :
    (X : Matrix n n k) *ᵥ (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_inv_mulVec_mulVec (X : GL n k) (v : n → k) :
    ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ ((X : Matrix n n k) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_conj_mulVec (X g : GL n k) (v : n → k) :
    ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v =
      (X : Matrix n n k) *ᵥ ((g : Matrix n n k) *ᵥ (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul]

theorem conj_fix_hyperplane_iff (X g : GL n k) (a : n → k) :
    (∀ v, a ⬝ᵥ v = 0 → ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v = v) ↔
      ∀ w, (a ᵥ* (X : Matrix n n k)) ⬝ᵥ w = 0 → (g : Matrix n n k) *ᵥ w = w := by
  constructor
  · intro h w hw
    have h1 := h ((X : Matrix n n k) *ᵥ w) (by rw [Matrix.dotProduct_mulVec]; exact hw)
    rw [gl_conj_mulVec, gl_inv_mulVec_mulVec] at h1
    have h2 := congrArg (fun u => ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ u) h1
    simpa only [gl_inv_mulVec_mulVec] using h2
  · intro h v hv
    rw [gl_conj_mulVec, h _ (by rw [← Matrix.dotProduct_mulVec, gl_mulVec_inv_mulVec]; exact hv),
      gl_mulVec_inv_mulVec]

theorem conj_triv_mod_line_iff (X g : GL n k) (a : n → k) :
    (∀ v, ∃ c : k, ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v - v = c • a) ↔
      ∀ w, ∃ c : k, (g : Matrix n n k) *ᵥ w - w = c • (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ a) := by
  constructor
  · intro h w
    obtain ⟨c, h1⟩ := h ((X : Matrix n n k) *ᵥ w)
    rw [gl_conj_mulVec, gl_inv_mulVec_mulVec] at h1
    have h2 := congrArg (fun u => ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ u) h1
    exact ⟨c, by simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, gl_inv_mulVec_mulVec] using h2⟩
  · intro h v
    obtain ⟨c, h1⟩ := h (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v)
    have h2 := congrArg (fun u => (X : Matrix n n k) *ᵥ u) h1
    refine ⟨c, ?_⟩
    rw [gl_conj_mulVec]
    simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, gl_mulVec_inv_mulVec] using h2

theorem vecMul_gl_ne_zero (X : GL n k) {a : n → k} (ha : a ≠ 0) : a ᵥ* (X : Matrix n n k) ≠ 0 := by
  intro h
  apply ha
  have h2 := congrArg (fun u => u ᵥ* ((X⁻¹ : GL n k) : Matrix n n k)) h
  simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one,
    Matrix.zero_vecMul] at h2
  exact h2

theorem gl_inv_mulVec_ne_zero (X : GL n k) {a : n → k} (ha : a ≠ 0) :
    ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ a ≠ 0 := by
  intro h
  apply ha
  rw [← gl_mulVec_inv_mulVec X a, h, Matrix.mulVec_zero]

theorem det_conj_gl (X g : GL n k) :
    Matrix.GeneralLinearGroup.det (X * g * X⁻¹) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem ite_congr_of_iff {p q : Prop} {dp : Decidable p} {dq : Decidable q} {u v : ℂ} (h : p ↔ q) :
    @ite ℂ p dp u v = @ite ℂ q dq u v := if_congr h rfl rfl

end Lin

theorem mirC_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ) (x : G), ∃ a' : Fin D.R.r → kP PP.1, a' ≠ 0 ∧ ∀ g, mirC R i PP a tr ε (x * g * x⁻¹) = mirC R i PP a' tr ε g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i PP a ha tr ε x
  have he : ∀ g PP', R.eG (x * g * x⁻¹) PP' = R.eG x PP' * R.eG g PP' * (R.eG x PP')⁻¹ := by
    intro g PP'
    rw [map_mul, map_mul, map_inv]
    rfl
  have h1 : ∀ g, (∀ PP', PP' ≠ PP → R.eG (x * g * x⁻¹) PP' = 1) ↔ ∀ PP', PP' ≠ PP → R.eG g PP' = 1 := by
    intro g
    refine forall_congr' fun PP' => forall_congr' fun _ => ?_
    rw [he, conj_eq_one_iff]
  have h2 : ∀ g, Matrix.GeneralLinearGroup.det (R.eG (x * g * x⁻¹) PP) = Matrix.GeneralLinearGroup.det (R.eG g PP) := by
    intro g
    rw [he]
    exact det_conj_gl _ _
  cases tr
  · refine ⟨_, vecMul_gl_ne_zero (R.eG x PP) ha, fun g => ?_⟩
    have h3 := conj_fix_hyperplane_iff (R.eG x PP) (R.eG g PP) a
    rw [← he] at h3
    unfold mirC
    rw [h2]
    refine ite_congr_of_iff (and_congr (h1 g) ?_)
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    exact h3
  · refine ⟨_, gl_inv_mulVec_ne_zero (R.eG x PP) ha, fun g => ?_⟩
    have h3 := conj_triv_mod_line_iff (R.eG x PP) (R.eG g PP) a
    rw [← he] at h3
    unfold mirC
    rw [h2]
    refine ite_congr_of_iff (and_congr (h1 g) ?_)
    rw [if_pos rfl, if_pos rfl]
    exact h3

end GlobalTheory.DownLift.GenFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParameters
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL.SphUniq

section Abstract

variable {G X V V' : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']

theorem map_eq_top {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hπ : π.IsIrreducible)
    (f : ρ.IntertwiningMap π) (U : Submodule ℂ X) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) {u : X} (hu : u ∈ U)
    (h0 : f u ≠ 0) (v : V) : ∃ x ∈ U, f x = v := by
  let R : Subrepresentation π := ⟨U.map f.toLinearMap, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, hU g x hx, f.isIntertwining _ _ g x⟩⟩
  rcases eq_bot_or_eq_top R with h | h
  · have h1 : f u ∈ R.toSubmodule := ⟨u, hu, rfl⟩
    rw [h] at h1
    exact absurd h1 h0
  · have h1 : v ∈ R.toSubmodule := by rw [h]; trivial
    exact h1

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem ker_le {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (f : ρ.IntertwiningMap π) (f' : ρ.IntertwiningMap π') {w : X} (hw : w ∈ fixed ρ K) (h0 : f w ≠ 0)
    (h0' : f' w ≠ 0) (hl : ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • w) :
    LinearMap.ker f.toLinearMap ≤ LinearMap.ker f'.toLinearMap := by
  intro u hu
  by_contra hu'
  obtain ⟨x, hx, e⟩ := map_eq_top hπ' f' (LinearMap.ker f.toLinearMap) (fun g y hy => by
    have hy' : f y = 0 := hy
    show f (ρ g y) = 0
    rw [f.isIntertwining, hy', map_zero]) hu hu' (f' w)
  have hx' : f x = 0 := hx
  obtain ⟨v, hv, ev⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK (f.toLinearMap.prod f'.toLinearMap) x fun g hg => by
    have h1 : ρ g w = w := by simpa using hw ⟨g, hg⟩
    refine Prod.ext ?_ ?_
    · show f (ρ g x) = f x
      rw [f.isIntertwining, hx', map_zero]
    · show f' (ρ g x) = f' x
      rw [f'.isIntertwining, e, ← f'.isIntertwining, h1]
  obtain ⟨c, rfl⟩ := hl v hv
  have e1 : f (c • w) = f x := congrArg Prod.fst ev
  have e2 : f' (c • w) = f' x := congrArg Prod.snd ev
  rw [hx', map_smul, smul_eq_zero] at e1
  rw [e1.resolve_right h0, zero_smul, map_zero, e] at e2
  exact h0' e2.symm

theorem equiv_of_line {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (f : ρ.IntertwiningMap π) (f' : ρ.IntertwiningMap π') {w : X} (hw : w ∈ fixed ρ K) (h0 : f w ≠ 0)
    (h0' : f' w ≠ 0) (hl : ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • w) : Nonempty (π.Equiv π') := by
  have hk := le_antisymm (ker_le hρ hπ' hK f f' hw h0 h0' hl) (ker_le hρ hπ hK f' f hw h0' h0 hl)
  have hs : Function.Surjective f.toLinearMap := fun v => by
    obtain ⟨x, -, e⟩ := map_eq_top hπ f ⊤ (fun _ _ _ => trivial) trivial h0 v
    exact ⟨x, e⟩
  have hs' : Function.Surjective f'.toLinearMap := fun v => by
    obtain ⟨x, -, e⟩ := map_eq_top hπ' f' ⊤ (fun _ _ _ => trivial) trivial h0' v
    exact ⟨x, e⟩
  let L : V ≃ₗ[ℂ] V' := (f.toLinearMap.quotKerEquivOfSurjective hs).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    f'.toLinearMap.quotKerEquivOfSurjective hs'
  have hL : ∀ x, L (f x) = f' x := fun x => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hs).symm (f x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [L, LinearEquiv.trans_apply, this]
    rfl
  refine ⟨Representation.Equiv.mk L fun g => LinearMap.ext fun v => ?_⟩
  obtain ⟨x, rfl⟩ := hs v
  show L (π g (f x)) = π' g (L (f x))
  rw [← f.isIntertwining, hL, hL, f'.isIntertwining]

theorem exists_vector {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap π)
    (hf : Function.Surjective f) (hs : fixed π K ≠ ⊥) :
    ∃ w : S.toSubmodule, w.1 ∈ fixed ρ K ∧ f w ≠ 0 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  have hS : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨S, .id _, Function.surjective_id⟩ hρ
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hS hK f.toLinearMap u fun h hh => by
    show f (S.toRepresentation h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  exact ⟨w, fun g => congrArg Subtype.val (hw g), fun h => hv0 (hfw.symm.trans h)⟩

theorem equiv_of_form {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (E : X →ₗ[ℂ] ℂ) (hE : ∀ u ∈ fixed ρ K, E u = 0 → u = 0) (h : IsSubquotient π ρ) (h' : IsSubquotient π' ρ)
    (hs : fixed π K ≠ ⊥) (hs' : fixed π' K ≠ ⊥) : Nonempty (π.Equiv π') := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨S', f', hf'⟩ := h'
  obtain ⟨w, hw, h0⟩ := exists_vector hρ hK S f hf hs
  obtain ⟨w', hw', h0'⟩ := exists_vector hρ hK S' f' hf' hs'
  have hl : ∀ z ∈ fixed ρ K, z ≠ 0 → ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • z := fun z hz hz0 v hv => by
    have hEz : E z ≠ 0 := fun e => hz0 (hE z hz e)
    refine ⟨E v / E z, sub_eq_zero.1 (hE _ (sub_mem hv (Submodule.smul_mem _ _ hz)) ?_)⟩
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hEz, sub_self]
  have hw0 : w.1 ≠ 0 := fun e => h0 (by rw [show w = 0 from Subtype.ext e, map_zero])
  have hw0' : w'.1 ≠ 0 := fun e => h0' (by rw [show w' = 0 from Subtype.ext e, map_zero])
  obtain ⟨c, hc⟩ := hl _ hw' hw0' _ hw
  have hc0 : c ≠ 0 := fun e => hw0 (by rw [hc, e, zero_smul])
  let R : Subrepresentation ρ := ⟨S.toSubmodule ⊓ S'.toSubmodule, fun g _ hv =>
    ⟨S.apply_mem_toSubmodule g hv.1, S'.apply_mem_toSubmodule g hv.2⟩⟩
  have hR : IsSmooth R.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨R, .id _, Function.surjective_id⟩ hρ
  let F : R.toRepresentation.IntertwiningMap π :=
    ⟨f.toLinearMap ∘ₗ Submodule.inclusion inf_le_left, fun g => LinearMap.ext fun x =>
      f.isIntertwining _ _ g (Submodule.inclusion inf_le_left x)⟩
  let F' : R.toRepresentation.IntertwiningMap π' :=
    ⟨f'.toLinearMap ∘ₗ Submodule.inclusion inf_le_right, fun g => LinearMap.ext fun x =>
      f'.isIntertwining _ _ g (Submodule.inclusion inf_le_right x)⟩
  have hm : w.1 ∈ S'.toSubmodule := hc ▸ Submodule.smul_mem _ _ w'.2
  refine equiv_of_line hR hπ hπ' hK F F' (w := ⟨w.1, w.2, hm⟩) (fun g => Subtype.ext (hw g)) h0 (fun e => ?_)
    fun v hv => ?_
  · have e1 : f' (c • w') = 0 := by
      rw [← e]
      exact congrArg f' (Subtype.ext hc.symm)
    rw [map_smul, smul_eq_zero] at e1
    exact e1.elim hc0 h0'
  · obtain ⟨d, hd⟩ := hl _ hw hw0 v.1 fun g => congrArg Subtype.val (hv g)
    exact ⟨d, Subtype.ext hd⟩

end Abstract

theorem equiv_of_parInd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (σ : Representation ℂ (Levi k m) ℂ)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (GL n k) V} {π' : Representation ℂ (GL n k) V'}
    (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) (h : IsSubquotient π (parInd e σ))
    (h' : IsSubquotient π' (parInd e σ)) (hs : IsSpherical π) (hs' : IsSpherical π') : Nonempty (π.Equiv π') := by
  let E : IndSp e σ →ₗ[ℂ] ℂ := ⟨⟨fun f => f.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  refine equiv_of_form (isSmooth_parInd e σ) hπ hπ' SplitFlip.isCompact_KO E (fun u hu h0 => ?_) h h' hs hs'
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  have h1 := congrArg (fun F : IndSp e σ => F.1.1 1) (hu ⟨c, hc⟩)
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul, one_mul] at h1
  have h2 : u.1.1 1 = 0 := h0
  rw [parInd_law, h1, h2, map_zero, smul_zero]
  rfl

theorem equiv_of_hasSatake : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (α : Fin n → ℂˣ) (π π' : IrrRep (GL (Fin n) k)), HasSatake π.ρ α → HasSatake π'.ρ α → Nonempty (π.ρ.Equiv π'.ρ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ h h' => equiv_of_parInd _ _ h.1 h'.1 h.2.2 h'.2.2 h.2.1 h'.2.1

end GlobalTheory.SmGL.SphUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocyclesBetweenBlochKatoAndContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

noncomputable def stPairs {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {V : Type} [AddCommGroup V]
    [Module ℚ_[l] V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) : Submodule ℚ_[l] ((↥(GK K) → V) × (V ⊗[ℚ_[l]] Bst P)) where
  carrier := {p | p.1 ∈ continuousCocycles ρ ∧ ∀ g, p.1 g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g p.2 - p.2}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hx⟩ ⟨hb, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, fun g => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, fun g => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

theorem exists_stCocycles_lower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v : V, Continuous fun g => ρ g v) → IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) → ∃ S : Submodule ℚ_[l] (↥(GK K) → V), finiteCocycles (P.PD K) ρ ≤ S ∧ S ≤ continuousCocycles ρ ∧ (∀ c ∈ S, ∃ z : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ (∀ c ∈ S, ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) ∧ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) ≤ finrank ℚ_[l] ↥S := by
  intro l _ P AI T K V _ _ _ _ _ _ _ V' _ _ _ ρ ρ' m hc hd hs hfin
  let π : ↥(stPairs P ρ) →ₗ[ℚ_[l]] (↥(GK K) → V) := (LinearMap.fst _ _ _).comp (stPairs P ρ).subtype
  let ν : ↥(stPairs P ρ) →ₗ[ℚ_[l]] (V ⊗[ℚ_[l]] Bst P) :=
    (monV P ℚ_[l] V).comp ((LinearMap.snd _ _ _).comp (stPairs P ρ).subtype)
  have hcris : ∀ (c : ↥(GK K) → V) (x : V ⊗[ℚ_[l]] P.R.B),
      (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ g x - x) →
      ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g (crisIncl P ℚ_[l] V x) - crisIncl P ℚ_[l] V x := by
    intro c x hx g
    rw [stRep_crisIncl, ← map_sub, ← hx, crisIncl_tmul, map_one]
  have h1 : finiteCocycles (P.PD K) ρ ≤ LinearMap.range π := by
    rintro c ⟨hc1, x, hx⟩
    exact ⟨⟨(c, crisIncl P ℚ_[l] V x), hc1, hcris c x hx⟩, rfl⟩
  have h2 : LinearMap.range π ≤ continuousCocycles ρ := by
    rintro _ ⟨e, rfl⟩
    exact e.2.1
  have h3 : ∀ c ∈ LinearMap.range π, ∃ z : V ⊗[ℚ_[l]] Bst P,
      ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := by
    rintro _ ⟨e, rfl⟩
    exact ⟨e.1.2, e.2.2⟩
  refine ⟨LinearMap.range π, h1, h2, h3, fun c hc => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := h3 c hc
    exact _root_.GlobalTheory.cocycle_dies_dR_of_dies_st l P AI T K V ρ c z hz
  have hφ : ∀ y ∈ Dst P ρ, phiV P ℚ_[l] V y ∈ Dst P ρ := fun y hy =>
    (mem_Dst P ρ).mpr fun g => by
      rw [← End.mul_apply, ← phiV_stRep, End.mul_apply, (mem_Dst P ρ).mp hy g]
  have hN : ∀ y ∈ Dst P ρ, monV P ℚ_[l] V y ∈ Dst P ρ := fun y hy =>
    (mem_Dst P ρ).mpr fun g => by
      rw [← End.mul_apply, ← monV_stRep, End.mul_apply, (mem_Dst P ρ).mp hy g]
  haveI := _root_.GlobalTheory.Pst.finiteDimensional_Dst_of_isSst l P K V ρ hs
  haveI : FiniteDimensional ℚ_[l] ↥(LinearMap.range π) := Submodule.finiteDimensional_of_le h2
  haveI : FiniteDimensional ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap
      ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := Submodule.finiteDimensional_of_le inf_le_left
  have h4 := _root_.GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le ℚ_[l] _ _ _ π ν (finiteCocycles (P.PD K) ρ) ((Dst P ρ).map (monV P ℚ_[l] V))
    (Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) h1
    (by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hN y hy, phiV P ℚ_[l] V y - y, Submodule.sub_mem _ (hφ y hy) hy, ?_⟩
      rw [map_sub, ← End.mul_apply, monV_phiV]
      rfl)
    (by
      rintro x ⟨hx, y, hy, hxy⟩
      obtain ⟨z, c, hc1, hc2, hz⟩ := _root_.GlobalTheory.semistable_class_of_pair l P AI T K V ρ hc x hx y hy hxy.symm
      exact ⟨⟨(c, z), hc1, hc2⟩, hz⟩)
    (by
      rintro e ⟨-, x, hx⟩
      refine ⟨e.1.2 - crisIncl P ℚ_[l] V x, (mem_Dst P ρ).mpr fun g => ?_, ?_⟩
      · have := (e.2.2 g).symm.trans (hcris _ x hx g)
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
        exact this
      · rw [map_sub, (_root_.GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl l P V _).mpr ⟨x, rfl⟩, sub_zero]
        rfl)
  have h5 := GlobalTheory.T.finrank_dcris_phi_fixed_add_finrank_mon_le_alt l P AI T K V V' ρ ρ' m hd hs
  omega

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilTsumEnormRationalInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.SWAbsInv

open GlobalTheory.RallisCusp

variable {D : D7}

def lagSwap (W : HSp D) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (LinearEquiv.prodComm D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)).toLinearMap, by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    exact (Y.2.2 y hy y' hy').symm⟩

theorem lagSwap_lagSwap (W : HSp D) (Y : Lag W) : lagSwap W (lagSwap W Y) = Y := by
  apply Subtype.ext
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hy
    exact ⟨y.swap, ⟨y, hy, rfl⟩, rfl⟩

theorem isLagFrame_lagSwap (W : HSp D) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) : IsLagFrame W (lagSwap W Y) (C.2, C.1) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (LinearEquiv.prodComm D.host.E _ _).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

theorem lagTerm_swap {V W : HSp D} (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (f₁ f₂ : WO V W → ℂ) :
    lagTerm μ 𝓕 (C.2, C.1) f₂ f₁ = star (lagTerm μ 𝓕 C f₁ f₂) := by
  unfold lagTerm
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [mul_comm]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}

theorem tsum_comm (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₂ f₁‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let e : Lag W ≃ Lag W := ⟨lagSwap W, lagSwap W, lagSwap_lagSwap W, lagSwap_lagSwap W⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₂ f₁ h₂ h₁).1 (lagSwap W Y) _
    (isLagFrame_lagSwap W Y (fr Y) (hS.frame Y))
  change ‖lagTerm μ 𝓕 (fr (lagSwap W Y)) f₂ f₁‖ₑ = _
  rw [← h, lagTerm_swap, ← ofReal_norm_eq_enorm, norm_star, ofReal_norm_eq_enorm]

theorem tsum_left (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ) f₁) f₂‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let g : GQ W := ⟨γ, hγ⟩
  let e : Lag W ≃ Lag W := ⟨lagAct W g, lagAct W g⁻¹,
    fun Y => by rw [← lagAct_mul, inv_mul_cancel, lagAct_one],
    fun Y => by rw [← lagAct_mul, mul_inv_cancel, lagAct_one]⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ f₂ (hS.weil.om_pres (1, γ) f₁ h₁) h₂).1
    (lagAct W g Y) _ (isLagFrame_lagAct W g Y (fr Y) (hS.frame Y))
  have h' := ((Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂).2 γ hγ (gqMat W g)
    (gqMat_map W g).symm).1 (fr Y)
  change ‖lagTerm μ 𝓕 (fr (lagAct W g Y)) (om (1, γ) f₁) f₂‖ₑ = _
  rw [← h, h']

end

theorem tsum_enorm_lagTerm_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS F₁ F₂ h₁ h₂ γ₁ hγ₁ γ₂ hγ₂
  have p₂ := hS.weil.om_pres (1, γ₂) F₂ h₂
  rw [tsum_left hS h₁ p₂ hγ₁, tsum_comm hS p₂ h₁, tsum_left hS h₂ h₁ hγ₂, tsum_comm hS h₁ h₂]

end GlobalTheory.SWAbsInv

end
end

