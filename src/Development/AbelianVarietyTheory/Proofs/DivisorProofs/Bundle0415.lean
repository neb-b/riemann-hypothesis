module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemLocalizationIffForallPrime
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationIntertwinesHeisenberg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistGeneratorTmulOrderLocally
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwMulOrder

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : Scheme.{0} → Prop} (h : Loc U P)
    (hPQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W _ => Q W) : Loc U fun W _ => Q W := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => hPQ V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun ⦃V⦄ ⦃g⦄ hg => T V g hg), ?_, ?_⟩
  · exact GrothendieckTopology.bind_covering _ hS (fun ⦃V⦄ ⦃g⦄ hg => hT V g hg)
  · rintro W _ ⟨V, k, g, hg, hk, -⟩
    exact hQ V g hg W k hk

def pgen (q : ℕ) (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) : (Scheme.Γ ⋙ twF q i).obj (op V) :=
  Submodule.Quotient.mk (Finsupp.single ζ 1)

theorem pgen_map (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    ((Scheme.Γ ⋙ twF q i).map g.op).hom (pgen q i ζ) = pgen q i (ζ.map g.appTop.hom) := by
  show Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (q := q) g.appTop.hom) (Finsupp.single ζ 1)) =
    (Submodule.Quotient.mk (Finsupp.single (ζ.map g.appTop.hom) 1) :
      (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(V, ⊤))
  rw [Finsupp.mapDomain_single]

theorem twGen_eq (q : ℕ) (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) :
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom (pgen q i ζ) = twGen i ζ := rfl

theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    ((tw q i).obj.map g.op).hom (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have h := congrArg (fun f => f.hom (pgen q i ζ))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [pgen_map] at h
  rw [← twGen_eq, ← twGen_eq]
  exact h.symm

theorem step_point (q : ℕ) [NeZero q] (i j : ℤ) (V : Scheme.{0}) [Nonempty V] (ζ : Prim q Γ(V, ⊤)) (c : ℕ)
    (h : c • (pgen q j ζ ⊗ₜ[ULift.{1} (ZMod q)] pgen q i ζ) = 0) : q ∣ c := by
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨Classical.arbitrary V, trivial⟩⟩
  haveI : Nontrivial Γ(V, ⊤) := Scheme.component_nontrivial V ⊤
  obtain ⟨fj, hfj⟩ := (GlobalTheory.TwFree.twist_free q j Γ(V, ⊤)).2 ζ
  obtain ⟨fi, hfi⟩ := (GlobalTheory.TwFree.twist_free q i Γ(V, ⊤)).2 ζ
  let fj' : (Scheme.Γ ⋙ twF q j).obj (op V) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) := fj
  let fi' : (Scheme.Γ ⋙ twF q i).obj (op V) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) := fi
  have e1 : fj' (pgen q j ζ) = 1 := hfj
  have e2 : fi' (pgen q i ζ) = 1 := hfi
  have h2 : (TensorProduct.lid (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)))
      (TensorProduct.map fj' fi' (c • (pgen q j ζ ⊗ₜ[ULift.{1} (ZMod q)] pgen q i ζ))) = 0 := by
    rw [h, map_zero, map_zero]
  rw [map_nsmul, map_nsmul, TensorProduct.map_tmul, e1, e2, TensorProduct.lid_tmul, one_smul] at h2
  have h3 : ((c : ZMod q)) = 0 := by
    have := congrArg ULift.down h2
    simpa using this
  exact (ZMod.natCast_eq_zero_iff c q).1 h3

theorem step_swap (q : ℕ) [NeZero q] (i j : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (c : ℕ)
    (h : c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] pgen q j ζ) = 0) : Loc V fun W _ => Nonempty W → q ∣ c := by
  have hφ := toSheafify_loc_bij_lift (ZMod q) (Scheme.Γ ⋙ twF q i)
  have key := (tensor_loc_bij (ZMod q) (Scheme.Γ ⋙ twF q j) (Scheme.Γ ⋙ twF q i) _
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) hφ.1 hφ.2.1 V).2
    (c • (pgen q j ζ ⊗ₜ pgen q i ζ)) (by
      rw [map_nsmul, LinearMap.lTensor_tmul, twGen_eq]
      have := congrArg (TensorProduct.comm _ _ _) h
      rwa [map_nsmul, TensorProduct.comm_tmul, map_zero] at this)
  refine loc_mono key ?_
  intro W g hg hW
  rw [map_nsmul, TensorProduct.map_tmul, pgen_map, pgen_map] at hg
  exact step_point q i j W (ζ.map g.appTop.hom) c hg

theorem tw_mul_order : ∀ (q : ℕ) [NeZero q] (i j : ℤ) (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ),
    c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c := by
  intro q _ i j W ζ c h
  have hφ := toSheafify_loc_bij_lift (ZMod q) (Scheme.Γ ⋙ twF q j)
  have key := (tensor_loc_bij (ZMod q) (tw q i).obj (Scheme.Γ ⋙ twF q j) _
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j)) hφ.1 hφ.2.1 W).2
    (c • (twGen i ζ ⊗ₜ pgen q j ζ)) (by rw [map_nsmul, LinearMap.lTensor_tmul, twGen_eq]; exact h)
  refine loc_bind key fun V g hg => step_swap q i j V (ζ.map g.appTop.hom) c ?_
  rw [map_nsmul, TensorProduct.map_tmul, pgen_map, twGen_res] at hg
  exact hg

end GlobalTheory.TwMulOrder

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

noncomputable section
namespace GlobalTheory.EtC.MuTw.Inj

variable (q : ℕ) [NeZero q]

theorem comp_appTop_apply' {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom a = g.appTop.hom (h.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem eq_zero_of_pow_eq_one {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (C : ZMod q)
    (h : ζ.1 ^ C.val = 1) : C = 0 := by
  by_contra hC
  have hne : ¬ C.val ≡ 0 [MOD q] := by
    intro hm
    apply hC
    rw [← ZMod.val_eq_zero]
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt C), Nat.zero_mod] at hm
  have hu := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).2.2.1 ζ C.val 0 hne
  rw [h, pow_zero, sub_self] at hu
  exact not_isUnit_zero hu

theorem mk_single_eq {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (c : ULift.{1} (ZMod q)) :
    (twRel q 1 A).mkQ (Finsupp.single ξ c) = (twRel q 1 A).mkQ (Finsupp.single ζ (c * ULift.up (a : ZMod q))) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have hmem : Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q)) ∈ twRel q 1 A :=
    Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have := (twRel q 1 A).smul_mem c hmem
  convert this using 1
  rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, zpow_one]

theorem mk_eq_single {A : Type} [CommRing A] (ζ : Prim q A) (f : Prim q A →₀ ULift.{1} (ZMod q))
    (h : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ C : ULift.{1} (ZMod q), (twRel q 1 A).mkQ f = (twRel q 1 A).mkQ (Finsupp.single ζ C) := by
  classical
  choose! a ha using h
  refine ⟨∑ ξ ∈ f.support, f ξ * ULift.up (a ξ : ZMod q), ?_⟩
  conv_lhs => rw [← Finsupp.sum_single f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum, Finsupp.single_finsetSum, map_sum]
  exact Finset.sum_congr rfl fun ξ hξ => mk_single_eq q ζ ξ (a ξ) (ha ξ hξ) (f ξ)

end GlobalTheory.EtC.MuTw.Inj

namespace GlobalTheory.EtC.MuTw.Inj
variable (q : ℕ) [NeZero q]

theorem local_zero (V : Scheme.{0}) [IsAffine V] (m : (twF q 1).obj Γ(V, ⊤))
    (hm : ((eta q).app Γ(V, ⊤)).hom m = 0) (v : V) :
    ∃ (W : Scheme.{0}) (k : W ⟶ V), IsAffine W ∧ Etale k ∧ v ∈ Set.range k ∧ ((twF q 1).map k.appTop).hom m = 0 := by
  classical
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (twRel q 1 Γ(V, ⊤)) m
  by_cases hf : f = 0
  · refine ⟨V, 𝟙 V, inferInstance, inferInstance, ⟨v, rfl⟩, ?_⟩
    have h0 : ((twRel q 1 Γ(V, ⊤)).mkQ f : (twF q 1).obj Γ(V, ⊤)) = 0 := by rw [hf, map_zero]
    rw [h0]
    exact map_zero _
  obtain ⟨ζ₀, hζ₀⟩ := Finsupp.support_nonempty_iff.2 hf
  let P : f.support → ∀ W : Scheme.{0}, (W ⟶ V) → Prop := fun ξ W k =>
    ∃ a : (ZMod q)ˣ, k.appTop.hom ξ.1.1 = k.appTop.hom ζ₀.1 ^ (a : ZMod q).val
  have hL : Loc V fun W k => ∀ ξ, P ξ W k :=
    (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.1 V f.support P fun ξ => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 ζ₀ ξ.1
  have hst : ∀ (W W' : Scheme.{0}) (g : W ⟶ V) (k : W' ⟶ W), (∀ ξ, P ξ W g) → ∀ ξ, P ξ W' (k ≫ g) := by
    intro W W' g k h ξ
    obtain ⟨a, ha⟩ := h ξ
    refine ⟨a, ?_⟩
    rw [comp_appTop_apply', comp_appTop_apply', ha, map_pow]
  obtain ⟨W, k, hWa, hk, ⟨w, hw⟩, hP⟩ := ((GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover V _ hst).1 hL) v
  refine ⟨W, k, hWa, hk, ⟨w, hw⟩, ?_⟩
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨w, trivial⟩⟩
  haveI : Nontrivial Γ(W, ⊤) := Scheme.component_nontrivial W ⊤
  let φ := k.appTop.hom
  let ζ₁ : Prim q Γ(W, ⊤) := Prim.map φ ζ₀
  have hmap : ((twF q 1).map k.appTop).hom ((twRel q 1 Γ(V, ⊤)).mkQ f) =
      (twRel q 1 Γ(W, ⊤)).mkQ (Finsupp.mapDomain (Prim.map φ) f) := rfl
  obtain ⟨C, hC⟩ := mk_eq_single q ζ₁ (Finsupp.mapDomain (Prim.map φ) f) (by
    intro ξ' hξ'
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hξ')
    obtain ⟨a, ha⟩ := hP ⟨ξ, hξ⟩
    exact ⟨a, ha⟩)
  rw [hmap, hC]
  have he : ((eta q).app Γ(W, ⊤)).hom ((twF q 1).map k.appTop |>.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0 := by
    have := congrArg (fun g => g.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) ((eta q).naturality k.appTop)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at this
    refine this.trans ?_
    change ((muF q).map k.appTop).hom (((eta q).app Γ(V, ⊤)).hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0
    rw [hm, map_zero]
  rw [hmap, hC, Submodule.mkQ_apply, eta_mk] at he
  have h1 : ζ₁.1 ^ C.down.val = 1 := by
    have := congrArg (fun y : ULift.{1} (Additive (rootsOfUnity q Γ(W, ⊤))) =>
      (((Additive.toMul y.down : rootsOfUnity q Γ(W, ⊤)) : Γ(W, ⊤)ˣ) : Γ(W, ⊤))) he
    simp only [smul_eq, toMul_nsmul, toMul_ofMul] at this
    rw [root_pow_coe] at this
    exact this.trans rfl
  have hC0 : C = 0 := ULift.ext (eq_zero_of_pow_eq_one q ζ₁ C.down h1)
  rw [hC0, Finsupp.single_zero, map_zero]
  rfl

end GlobalTheory.EtC.MuTw.Inj

namespace GlobalTheory.EtC.MuTw.Inj

theorem res_comp {q : ℕ} {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (x : Sec (tw q 1) U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  change ((tw q 1).obj.map (k ≫ g).op).hom x = ((tw q 1).obj.map k.op).hom (((tw q 1).obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem etaS_injective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Function.Injective ((etaS q).hom.app (op U)).hom := by
  intro q _ U _
  refine (injective_iff_map_eq_zero ((etaS q).hom.app (op U)).hom).2 fun x hx => ?_
  have hst : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), Sec.res g x = 0 → Sec.res (k ≫ g) x = 0 := by
    intro V W g k h
    rw [res_comp, h]
    exact map_zero _
  have hloc : Loc U fun W g => Sec.res g x = 0 := by
    rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ hst]
    intro u
    obtain ⟨V, j, v, m, hVa, hj, hjv, hm⟩ := (GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) U).1 x u
    have hem : ((eta q).app Γ(V, ⊤)).hom m = 0 := by
      have hm' : (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) = Sec.res (F := tw q 1) j x := hm
      rw [← etaS_sec, hm', etaS_res]
      change Sec.res j (((etaS q).hom.app (op U)).hom x) = 0
      rw [hx]
      exact map_zero _
    obtain ⟨W, k, hWa, hk, ⟨w, hw⟩, hmW⟩ := local_zero q V m hem v
    refine ⟨W, k ≫ j, hWa, inferInstance, ⟨w, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hw, hjv]
    · have hm' : Sec.res (F := tw q 1) j x = (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) := hm.symm
      rw [res_comp, hm']
      refine ((GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) V).2.2 W k m).trans ?_
      rw [hmW]
      exact map_zero _
  obtain ⟨S, hS, hSP⟩ := hloc
  have hF := (tw q 1).property
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hF
  refine (hF S hS).isSeparatedFor.ext fun V g hg => ?_
  have h1 := hSP V g hg
  change Sec.res g x = Sec.res g 0
  rw [h1]
  exact (map_zero _).symm

end GlobalTheory.EtC.MuTw.Inj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimitsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits : ∀ (q : ℕ) (i : ℤ), PreservesFilteredColimitsOfSize.{0, 0} (twF q i) := by
  first | (exact @GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits) | (exact GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits) | (intros; apply GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralSche
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.OpenImmDim

theorem topologicalKrullDim_eq_of_isOpenImmersion : ∀ (F : Type) [Field F] (X V : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ]
    [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by
  intro F _ X V _ p ℓ _ _ _
  have hne : ((ℓ.opensRange : X.Opens) : Set X).Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨ℓ v, by rw [Scheme.Hom.coe_opensRange]; exact ⟨v, rfl⟩⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F p ℓ.opensRange hne]
  exact (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding ℓ.isOpenEmbedding.isEmbedding
    (by rw [Scheme.Hom.coe_opensRange])).symm

end GlobalTheory.OpenImmDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreDimQuotientPDivGroupLevelStatement
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ),
      1 ≤ k → ∀ (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] [Module.Finite O B]
        [Module.Projective O B] (j : B →ₐc[O] G.A (k + m)) (ρ : G.A (k + m) →ₗ[O] B),
        (∀ b, ρ (j b) = b) → torsionIdeal (R := O) (A := G.A (k + m)) p ≤ kerIdeal j →
        ∀ q : PrimeSpectrum O,
          fibreDim (B ⧸ torsionIdeal (R := O) (A := B) (p ^ m)) q = p ^ (m * G.height) := by
  intro p _ O _ G k m hk B _ _ _ _ _ j ρ hρ hj q
  obtain ⟨r, μ, hr, hker, hμ, hμq⟩ := G.exists_mulPow_fibreRank_eq p O k m
  let jₗ := (j : B →ₐ[O] G.A (k + m)).toLinearMap
  let rjₗ := ((r.comp j) : B →ₐ[O] G.A k).toLinearMap
  let μₗ := (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap
  let mul := mulBy (R := O) (A := B) (p ^ m)
  let mulₗ := (mul : B →ₐ[O] B).toLinearMap
  have hjq : fibreRank jₗ q = fibreDim B q :=
    (FibreRanks.fibre_ranks O B (G.A (k + m)) (G.A (k + m)) jₗ).1 ρ hρ q
  have hlevel := fibreDim_eq_ker_mul_range j q
  rw [show fibreRank (j : B →ₐ[O] G.A (k + m)).toLinearMap q = _ from hjq, G.fibreDim_eq]
    at hlevel
  have hres := fibreDim_eq_ker_mul_range (r.comp j) q
  rw [G.fibreDim_eq] at hres
  have hle : RingHom.ker r ≤ kerIdeal j := by
    rw [hker]
    exact (torsionIdeal_le_of_dvd (dvd_pow_self p (by omega : k ≠ 0))).trans hj
  let J := kerIdeal (r.comp j)
  let φ : G.A (k + m) →ₐ[O] G.A k ⧸ J := (Ideal.Quotient.mkₐ O J).comp r
  have hφ : Function.Surjective φ := (Ideal.Quotient.mkₐ_surjective O J).comp hr
  have hkerφ : RingHom.ker φ = kerIdeal j := by
    have hcomap : RingHom.ker φ = J.comap (r : G.A (k + m) →ₐ[O] G.A k) := by
      ext a
      simp [φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hcomap, show J = Ideal.map (r : G.A (k + m) →ₐ[O] G.A k) (kerIdeal j) from
      kerIdeal_comp r j, Ideal.comap_map_of_surjective (r : G.A (k + m) →ₐ[O] G.A k) hr,
      sup_eq_left]
    exact hle
  let e : (G.A (k + m) ⧸ kerIdeal j) ≃ₗ[O] (G.A k ⧸ J) :=
    ((Ideal.quotientEquivAlgOfEq O hkerφ).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
  rw [← fibreDim_congr e q] at hres
  have hmul := fibreDim_eq_ker_mul_range mul q
  have hlin : jₗ ∘ₗ mulₗ = μₗ ∘ₗ rjₗ := by
    ext b
    change j (mulBy (R := O) (A := B) (p ^ m) b) = μ (r (j b))
    rw [map_mulBy, hμ]
  have hrank : fibreRank mulₗ q = fibreRank rjₗ q := by
    rw [← (FibreRanks.fibre_ranks O B B (G.A (k + m)) mulₗ).2.1 jₗ q hjq, hlin,
      (FibreRanks.fibre_ranks O B (G.A k) (G.A (k + m)) rjₗ).2.1 μₗ q (hμq q)]
  change fibreDim B q = fibreDim (B ⧸ kerIdeal mul) q * fibreRank mulₗ q at hmul
  rw [hrank] at hmul
  change fibreDim (B ⧸ kerIdeal mul) q = _
  have hp : 0 < p ^ (k * G.height) := pow_pos (Fact.out : p.Prime).pos _
  have hpow : p ^ ((k + m) * G.height) = p ^ (m * G.height) * p ^ (k * G.height) := by
    rw [Nat.add_mul, pow_add, mul_comm]
  refine (Nat.eq_of_mul_eq_mul_right hp ?_).symm
  rw [← hpow, hlevel, hmul, hres]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemLocalizationIffForallPrimeStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_mem_localization_iff_forall_prime_alt : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ t : A, Irreducible t → p = Ideal.span {t} → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1) → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e)) → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∀ (s : B) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  first | (exact @GlobalTheory.CodimDual.trace_mem_localization_iff_forall_prime) | (exact GlobalTheory.CodimDual.trace_mem_localization_iff_forall_prime) | (intros; apply GlobalTheory.CodimDual.trace_mem_localization_iff_forall_prime  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerSumsModularFamilies
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem sum_prod_pow_div_pow {ι S : Type} [Fintype ι] [Fintype S] (m μ : S → ℕ) (x : S → ι → ℂ)
    (ω : ℂ) :
    (∑ i, ∏ s, x s i ^ μ s) / ω ^ (∑ s, μ s * m s) = ∑ i, ∏ s, (x s i / ω ^ m s) ^ μ s := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  simp only [mul_comm]

theorem transport_power_sums : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ μ : S → ℕ, ∑ i, ∏ s, g (f s i τ₀ / ω₀ ^ m s) ^ μ s = ∑ i, ∏ s, (f' s i τ₁ / ω₁ ^ m s) ^ μ s := by
  intro g ι S _ _ act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hfam hq h4 h6 μ
  obtain ⟨-, -, -, -, hpow, -, hprod, -⟩ := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act
  obtain ⟨-, -, -, -, qpow, qfin⟩ := _root_.GlobalTheory.QFam.qConj_ring g N hN
  have hM : IsFam act (((∑ s, μ s * m s : ℕ) : ℤ)) fun i τ => ∏ s, f s i τ ^ μ s := by
    have := hprod S Finset.univ (fun s => (μ s : ℤ) * (m s : ℤ)) (fun s i τ => f s i τ ^ μ s)
      (fun s _ => hpow (m s) (f s) (μ s) (hfam s))
    push_cast
    exact this
  have hQ : QConj g N (fun τ => ∑ i, ∏ s, f s i τ ^ μ s) fun τ => ∑ i, ∏ s, f' s i τ ^ μ s :=
    (qfin ι Finset.univ (fun i τ => ∏ s, f s i τ ^ μ s) (fun i τ => ∏ s, f' s i τ ^ μ s)
      fun i _ => (qfin S Finset.univ (fun s τ => f s i τ ^ μ s) (fun s τ => f' s i τ ^ μ s)
        fun s _ => qpow _ _ (μ s) (hq s i)).2).1
  have key := _root_.GlobalTheory.QFam.levelOne_value_transport g (∑ s, μ s * m s) N _ _ τ₀ τ₁ ω₀ ω₁ hN
    (fun γ => (_root_.GlobalTheory.QFam.sum_esymm_slash ι act _ _ hact hM γ).1) hQ h4 h6
  rw [sum_prod_pow_div_pow m μ (fun s i => f s i τ₀), sum_prod_pow_div_pow m μ (fun s i => f' s i τ₁)] at key
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_prod, map_pow] using key

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTensorWidePullbackLimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_tensor_wide_pullback_limit : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (2 + 1) => GlobalTheory.CechOne.fB A B) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B))))) (GlobalTheory.CechOne.y2 A B) (GlobalTheory.CechOne.hy2 A B))) := by
  first | (exact @GlobalTheory.CechOne.spec_tensor3_isLimit) | (exact GlobalTheory.CechOne.spec_tensor3_isLimit) | (intros; apply GlobalTheory.CechOne.spec_tensor3_isLimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationIntertwinesHeisenbergStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_intertwines_heisenberg : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E), Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) := by
  first | exact @GlobalTheory.KSp.weil_heis_intertwine | exact GlobalTheory.KSp.weil_heis_intertwine | (intros; apply GlobalTheory.KSp.weil_heis_intertwine <;> assumption)
end

