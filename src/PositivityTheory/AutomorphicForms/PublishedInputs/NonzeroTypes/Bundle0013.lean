module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothStabiliserSubgroup
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace SmoothStabiliserSubgroup

theorem rightReg_apply' {K : Type} [Group K] (k' : K) (φ : K → ℂ) (g : K) :
    rightReg ℂ K ℂ k' φ g = φ (g * k') := rfl

def stab {K : Type} [Group K] (φ : K → ℂ) : Subgroup K where
  carrier := {k' | rightReg ℂ K ℂ k' φ = φ}
  one_mem' := by
    show rightReg ℂ K ℂ 1 φ = φ
    funext g
    rw [rightReg_apply', mul_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : rightReg ℂ K ℂ a φ = φ := ha
    have hb' : rightReg ℂ K ℂ b φ = φ := hb
    show rightReg ℂ K ℂ (a * b) φ = φ
    funext g
    have h1 := congrFun hb' (g * a)
    have h2 := congrFun ha' g
    rw [rightReg_apply'] at h1 h2 ⊢
    rw [← mul_assoc, h1, h2]
  inv_mem' := by
    intro a ha
    have ha' : rightReg ℂ K ℂ a φ = φ := ha
    show rightReg ℂ K ℂ a⁻¹ φ = φ
    funext g
    have h1 := congrFun ha' (g * a⁻¹)
    rw [rightReg_apply', inv_mul_cancel_right] at h1
    rw [rightReg_apply']
    exact h1.symm

end SmoothStabiliserSubgroup

theorem smoothVectorsFixed_holds : SmoothVectorsFixedByCongruence := by
  intro k _ _ _ _ n G hKC h1 φ hφ
  have hU : IsOpen ((Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev) :=
    hKC.preimage continuous_subtype_val
  have hsub : (Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev ⊆
      (SmoothStabiliserSubgroup.stab φ : Set ↥(KO k (Fin n))) := by
    intro u hu
    show rightReg ℂ ↥(KO k (Fin n)) ℂ u φ = φ
    funext g
    rw [SmoothStabiliserSubgroup.rightReg_apply']
    exact hφ.2 g u hu
  have h1mem : (1 : ↥(KO k (Fin n))) ∈ (Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev := h1
  have hn : (SmoothStabiliserSubgroup.stab φ : Set ↥(KO k (Fin n))) ∈ nhds (1 : ↥(KO k (Fin n))) :=
    Filter.mem_of_superset (hU.mem_nhds h1mem) hsub
  exact (SmoothStabiliserSubgroup.stab φ).isOpen_of_mem_nhds hn

end UpperTheory.NonzeroTypeTheory
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Subquotient2
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.Subquotient₂

variable {F H V : Type} [Field F] [Group H] [AddCommGroup V] [Module F V]

theorem wellFoundedGT_of_finiteLength {ρ : Representation F H V} (h : HasFiniteLength ρ) :
    WellFoundedGT (Subrepresentation ρ) := by
  have hN := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
  have := isNoetherian_iff'.mp hN
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedGT

theorem wellFoundedLT_of_finiteLength {ρ : Representation F H V} (h : HasFiniteLength ρ) :
    WellFoundedLT (Subrepresentation ρ) := by
  have hA := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2
  have : WellFoundedLT (Submodule (MonoidAlgebra F H) ρ.asModule) := hA
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedLT

theorem exists_covBy {ρ : Representation F H V} (h : HasFiniteLength ρ) {y : V} (hy : y ≠ 0) :
    ∃ S T : Subrepresentation ρ, T ⋖ S ∧ y ∈ S.toSubmodule ∧ y ∉ T.toSubmodule := by
  have := wellFoundedGT_of_finiteLength h
  have := wellFoundedLT_of_finiteLength h
  obtain ⟨T, hT, hmax⟩ := wellFounded_gt.has_min {T : Subrepresentation ρ | y ∉ T.toSubmodule}
    ⟨⊥, fun h' => hy ((Submodule.mem_bot F).1 h')⟩
  have hTtop : T ≠ ⊤ := by
    rintro rfl
    exact hT trivial
  obtain ⟨S, hS, hmin⟩ := wellFounded_lt.has_min {S : Subrepresentation ρ | T < S}
    ⟨⊤, lt_top_iff_ne_top.2 hTtop⟩
  refine ⟨S, T, ⟨hS, fun U hTU hUS => hmin U hTU hUS⟩, ?_, hT⟩
  by_contra hyS
  exact hmax S hyS hS

end UpperTheory.TNZ.Grp.Subquotient₂

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_subq {n : ℕ} (G : Grp k n) : G.SubquotientProp := by
  intro W _ _ ρ hs hfl hη
  obtain ⟨y, hy, hyη⟩ := hη
  obtain ⟨S, T, hcov, hyS, hyT⟩ := Subquotient₂.exists_covBy hfl hy
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
  refine ⟨_, inferInstance, inferInstance, subQuot S T, hsq.isSmooth hs, isIrreducible_subQuot hcov, hsq,
    Submodule.Quotient.mk ⟨y, hyS⟩, ?_, fun m hm => ?_⟩
  · rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hyT
  · show Submodule.Quotient.mk (S.toRepresentation m ⟨y, hyS⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hyη m hm)

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Tensor2
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct
open Module

namespace UpperTheory.TNZ.Grp.Tensor₂

section Contr

variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {Y : ι → Type} [∀ b, AddCommGroup (Y b)]
  [∀ b, Module ℂ (Y b)]

theorem prod_update (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) (x : ∀ b, Y b) (i : ι) (hi : i ≠ a) (w : Y i) :
    ∏ b ∈ Finset.univ.erase a, φ b (Function.update x i w b) =
      φ i w * ∏ b ∈ (Finset.univ.erase a).erase i, φ b (x b) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]

theorem prod_update_self (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) (x : ∀ b, Y b) (w : Y a) :
    ∏ b ∈ Finset.univ.erase a, φ b (Function.update x a w b) = ∏ b ∈ Finset.univ.erase a, φ b (x b) :=
  Finset.prod_congr rfl fun b hb => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]

def contrML (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) : (∀ b, Y b) →ₘₗ[ℂ] Y a where
  toFun x := (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a
  map_update_add' := by
    intro inst x i u v
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = a
    · subst h
      simp only [prod_update_self, Function.update_self, smul_add]
    · simp only [prod_update a φ x i h, Function.update_of_ne (Ne.symm h), map_add (f := _), add_mul, add_smul]
  map_update_smul' := by
    intro inst x i c u
    obtain rfl : inst = hd := Subsingleton.elim _ _
    simp only [RingHom.id_apply]
    by_cases h : i = a
    · subst h
      simp only [prod_update_self, Function.update_self]
      rw [smul_comm]
    · simp only [prod_update a φ x i h, Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul]
      rw [mul_assoc, mul_smul]

def contr (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) : (⨂[ℂ] b, Y b) →ₗ[ℂ] Y a :=
  PiTensorProduct.lift (contrML a φ)

theorem contr_tprod (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) (x : ∀ b, Y b) :
    contr a φ (PiTensorProduct.tprod ℂ x) = (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a := by
  rw [contr, PiTensorProduct.lift.tprod]
  rfl

theorem exists_factor_vec {Γ : ι → Type} [∀ b, Group (Γ b)] (ρ : ∀ b, Representation ℂ (Γ b) (Y b)) (a : ι)
    (y : ⨂[ℂ] b, Y b) (hy : y ≠ 0) (S : Set (Γ a)) (c : Γ a → ℂ)
    (h : ∀ g ∈ S, piTensor ρ (Pi.mulSingle a g) y = c g • y) :
    ∃ v : Y a, v ≠ 0 ∧ ∀ g ∈ S, ρ a g v = c g • v := by
  let bs := fun b => Module.Basis.ofVectorSpace ℂ (Y b)
  let B := Basis.piTensorProduct bs
  obtain ⟨p, hp⟩ : ∃ p, B.repr y p ≠ 0 := by
    by_contra H
    simp only [not_exists, not_not] at H
    refine hy (B.repr.injective ?_)
    ext p
    rw [H p, map_zero, Finsupp.zero_apply]
  let φ : ∀ b, Module.Dual ℂ (Y b) := fun b => (bs b).coord (p b)
  have key : ∀ z, (bs a).coord (p a) (contr a φ z) = B.repr z p := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [map_smul, contr_tprod, B, Basis.piTensorProduct_repr_tprod_apply, Finsupp.smul_apply,
        smul_eq_mul, Basis.coord_apply, φ]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
      ring
    | add z w hz hw => rw [map_add (f := _), map_add (f := _), hz, hw, map_add (f := _), Finsupp.add_apply]
  have hequiv : ∀ g z, contr a φ (piTensor ρ (Pi.mulSingle a g) z) = ρ a g (contr a φ z) := by
    intro g z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      have hpr : ∏ b ∈ Finset.univ.erase a, φ b (ρ b (Pi.mulSingle a g b) (x b)) =
          ∏ b ∈ Finset.univ.erase a, φ b (x b) := by
        refine Finset.prod_congr rfl fun b hb => ?_
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb), map_one, Module.End.one_apply]
      simp only [map_smul, piTensor_tprod, contr_tprod, Pi.mulSingle_eq_same, hpr]
    | add z w hz hw => simp only [map_add (f := _), hz, hw]
  refine ⟨contr a φ y, fun h0 => hp ?_, fun g hg => ?_⟩
  · rw [← key, h0, map_zero]
  · rw [← hequiv, h g hg, map_smul]

end Contr

end UpperTheory.TNZ.Grp.Tensor₂

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_tensor {n : ℕ} (G : Grp k n) : G.TensorProductProp := by
  intro hN X _ _ σ hs hirr hη
  obtain ⟨y, hy0, hy⟩ := hη
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hN.loc.bz k (Fin G.s)
    (fun a => Fin (G.d a)) { V := X, ρ := σ, smooth := hs, irr := hirr }
  refine ⟨fun a => (s a).V, fun a => inferInstance, fun a => inferInstance, fun a => (s a).ρ,
    fun a => (s a).smooth, fun a => (s a).irr, fun a => ?_, ⟨E⟩⟩
  have hE : ∀ m, E (σ m y) = piTensor (fun b => (s b).ρ) m (E y) := fun m =>
    LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' m) y
  have hEy : E y ≠ 0 := (map_ne_zero_iff E (EquivLike.injective E)).2 hy0
  have hK : ∀ g ∈ (KO k (Fin (G.d a)) : Set (GL (Fin (G.d a)) k)),
      piTensor (fun b => (s b).ρ) (Pi.mulSingle a g) (E y) =
        ((G.μ a (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • E y := by
    intro g hg
    have hm : (Pi.mulSingle a g : Levi k fun b : Fin G.s => Fin (G.d b)) ∈
        leviK k (m := fun b : Fin G.s => Fin (G.d b)) := by
      rw [leviK, Subgroup.mem_pi]
      intro b _
      by_cases hb : b = a
      · subst hb
        rw [Pi.mulSingle_eq_same]
        exact hg
      · rw [Pi.mulSingle_eq_of_ne hb]
        exact one_mem _
    rw [← hE, hy _ hm, map_smul]
    congr 1
    rw [eta, Finset.prod_eq_single a]
    · rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one, Units.val_one]
    · intro h
      exact absurd (Finset.mem_univ a) h
  exact Tensor₂.exists_factor_vec (fun b => (s b).ρ) a (E y) hEy _ _ hK

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TwistedSphericalEquivalence
section
noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace TwistedSphericalEquivalence

theorem isTwSphProd_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (e : ρ.Equiv ρ')
    {s : ℕ} {d : Fin s → ℕ} {hd : ∑ a, d a = n} {η : Fin s → kˣ →* ℂˣ}
    (h : UpperTheory.TNZ.IsTwSphProd ρ' d hd η) : UpperTheory.TNZ.IsTwSphProd ρ d hd η := by
  obtain ⟨X, i1, i2, σ, hs, hi, hv, ⟨φ⟩⟩ := h
  exact ⟨X, i1, i2, σ, hs, hi, hv, ⟨Representation.Equiv.trans e φ⟩⟩

end TwistedSphericalEquivalence

theorem twistedSphericalRepresentative_holds : TwistedSphericalRepresentative := by
  intro k _ _ _ _ n V _ _ ρ h1 h2 s d hd η
  have e := GlobalTheory.LocGL.IrrGL.equivOf ρ h1 h2
  exact ⟨fun h => TwistedSphericalEquivalence.isTwSphProd_of_equiv e h, fun h => TwistedSphericalEquivalence.isTwSphProd_of_equiv (Representation.Equiv.symm e) h⟩

end UpperTheory.NonzeroTypeTheory
end
end

