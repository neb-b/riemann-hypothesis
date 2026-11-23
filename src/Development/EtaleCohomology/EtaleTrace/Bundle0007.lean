module

public import Development.EtaleCohomology.EtaleTrace.Bundle0004

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfTwistCoverCocycle
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem freeGen_nat (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x : uliftFunctor.{1, 0}.obj (P.obj (op U)))))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  simp only [Sec.res, freeGen]
  refine h.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)))
    (by simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map]
        exact Finsupp.mapDomain_single)

theorem evNat : EvNat := by
  intro R _ F X U α x
  have h := freeGen_nat R ((sch.obj X).obj (op (SimplexCategory.mk 0))) x (𝟙 X : Sx (sch.obj X) 0 X)
  have hx : ((sch.obj X).obj (op (SimplexCategory.mk 0))).map x.op (𝟙 X : Sx (sch.obj X) 0 X) = (x : Sx (sch.obj X) 0 U) :=
    Category.comp_id x
  rw [hx] at h
  simp only [ev]
  rw [← h]
  simp only [Sec.res]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.TwZeroPfGlue
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

theorem tz_sec_eq_of_loc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated F U S hS y z (fun _ g hg => hP _ g hg)

theorem tz_twGen_eq_of_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen (q := q) 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

def PrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
  Loc U fun V g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val

theorem TwZero_of_primLoc (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hP : PrimLoc) : TwZero := by
  intro q _ U ζ ξ
  obtain ⟨-, -, T3⟩ := hTw q 0
  apply tz_sec_eq_of_loc
  obtain ⟨S, hS, hP'⟩ := hP q U ζ ξ
  refine ⟨S, hS, fun _ g hg => ?_⟩
  obtain ⟨a, ha⟩ := hP' _ g hg
  rw [T3, T3]
  exact (tz_twGen_eq_of_pow _ _ a ha).symm

end LateralTheory.EtaleTrace
end
end

