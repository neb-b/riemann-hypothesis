module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0037
public import Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.EtaleCohomology.EtaleSheaves.Bundle0038
public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.TwTrivPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.TwistTrivial

theorem genRes {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun φ => φ.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (((Scheme.Γ ⋙ twF q i).map g.op).hom _) = _
  congr 1
  exact congrArg Submodule.Quotient.mk Finsupp.mapDomain_single

theorem prim_map_comp {q : ℕ} {X Y S : Scheme.{0}} (ζ : Prim q Γ(S, ⊤)) (s : X ⟶ S) (f : Y ⟶ X) :
    (ζ.map s.appTop.hom).map f.appTop.hom = ζ.map (f ≫ s).appTop.hom := by
  apply Subtype.ext
  change f.appTop.hom (s.appTop.hom ζ.1) = (f ≫ s).appTop.hom ζ.1
  rw [Scheme.Hom.comp_appTop]
  rfl

def Mul : Prop := ∀ (q : ℕ), ∃ μ : ∀ (j k l : ℤ), j + k = l → ∀ (X : Scheme.{0}), Sec (tw q k) X → (Sec (tw q j) X →+ Sec (tw q l) X),
  (∀ (j k l : ℤ) (h : j + k = l) {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Sec (tw q k) X) (x : Sec (tw q j) X),
      Sec.res f (μ j k l h X y x) = μ j k l h Y (Sec.res f y) (Sec.res f x)) ∧
  (∀ (j k l k' : ℤ) (h : j + k = l) (h' : l + k' = j) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (x : Sec (tw q j) X),
      μ l k' j h' X (twGen k' ζ) (μ j k l h X (twGen k ζ) x) = x)

theorem TwTriv_of (hM : Mul) : LateralTheory.E.LCIsoPf.TwTriv := by
  intro q i S ζ
  obtain ⟨μ, hnat, hcan⟩ := hM q
  refine ⟨fun X s => AddEquiv.mk' ⟨μ 0 i i (zero_add i) X (twGen i (ζ.map s.appTop.hom)),
      μ i (-i) 0 (add_neg_cancel i) X (twGen (-i) (ζ.map s.appTop.hom)),
      fun x => hcan 0 i i (-i) (zero_add i) (add_neg_cancel i) X _ x,
      fun y => hcan i (-i) 0 i (add_neg_cancel i) (zero_add i) X _ y⟩ (fun a b => map_add (μ 0 i i (zero_add i) X (twGen i (ζ.map s.appTop.hom))) a b), ?_⟩
  intro X Y s t f hf x
  change Sec.res f (μ 0 i i _ X _ x) = μ 0 i i _ Y _ (Sec.res f x)
  rw [hnat, genRes, prim_map_comp, hf]

end LateralTheory.E.TwistTrivial
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.UnitSections
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.UnitSections

theorem powLocal : LateralTheory.E.LeafUnitSecPf.Indep.LeafPowLocal := by
  intro q _ U ζ ξ
  obtain ⟨s, hs, hf⟩ := LateralTheory.E.L_prim_locPf.algPow q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hS, hP⟩ := LateralTheory.E.L_prim_locPf.loc_of_span s hs
    (P := fun V g => ∃ a : (ZMod q)ˣ,
      (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val) (by
      intro f hfs V g hu
      obtain ⟨a, n, hn⟩ := hf f hfs
      refine ⟨a, ?_⟩
      have h := LateralTheory.E.L_prim_locPf.eq_of_unit_kill g.appTop.hom hn hu
      rw [map_pow] at h
      exact h)
  exact ⟨S, hS, hP⟩

theorem LeafUnitSec_of : LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.Indep.LeafUnitSec_of LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of powLocal

end LateralTheory.E.UnitSections
end
end

