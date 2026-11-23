module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ComapSurjOfLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.KummerTwistLemmas
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace KummerTwistLemmas

theorem twLift {Q : ℕ} [NeZero Q] (i : ℤ) (G : Shv (ZMod Q)) (e : ∀ (U : Scheme.{0}), Prim Q Γ(U, ⊤) → Sec G U)
    (he : ∀ {V U : Scheme.{0}} (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom))
    (hr : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = (ULift.up ((a ^ i : (ZMod Q)ˣ) : ZMod Q) : ULift.{1} (ZMod Q)) • e U ζ) :
    ∃ f : tw Q i ⟶ G, ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map f (twGen i ζ) = e U ζ := by
  let L : ∀ (U : Scheme.{0}), (Prim Q Γ(U, ⊤) →₀ ULift.{1} (ZMod Q)) →ₗ[ULift.{1} (ZMod Q)] Sec G U :=
    fun U => Finsupp.linearCombination (ULift.{1} (ZMod Q)) (e U)
  have hL : ∀ (U : Scheme.{0}), twRel Q i Γ(U, ⊤) ≤ LinearMap.ker (L U) := by
    intro U
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, h, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L, Finsupp.linearCombination_single, one_smul]
    rw [hr U ζ ξ a h, sub_self]
  let η : (Scheme.Γ ⋙ twF Q i) ⟶ G.obj :=
    { app := fun U => ModuleCat.ofHom ((twRel Q i Γ(U.unop, ⊤)).liftQ (L U.unop) (hL U.unop))
      naturality := fun U V g => by
        refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ c => ?_))
        change (twRel Q i Γ(V.unop, ⊤)).liftQ (L V.unop) (hL V.unop)
            (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g).hom) (Finsupp.single ζ c))) =
          (G.obj.map g).hom ((twRel Q i Γ(U.unop, ⊤)).liftQ (L U.unop) (hL U.unop) (Submodule.Quotient.mk (Finsupp.single ζ c)))
        rw [Submodule.liftQ_apply, Submodule.liftQ_apply, Finsupp.mapDomain_single]
        simp only [L, Finsupp.linearCombination_single, map_smul]
        congr 1
        exact (he g.unop ζ).symm }
  refine ⟨((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} (ZMod Q)))).homEquiv _ _).symm η,
    fun U ζ => ?_⟩
  have h := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} (ZMod Q)))).homEquiv _ G).apply_symm_apply η
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) h)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim Q Γ(U, ⊤) →₀ ULift.{1} (ZMod Q)) ⧸ twRel Q i Γ(U, ⊤))
  refine h2.trans ?_
  change (twRel Q i Γ(U, ⊤)).liftQ (L U) (hL U) (Submodule.Quotient.mk (Finsupp.single ζ 1)) = e U ζ
  rw [Submodule.liftQ_apply]
  simp [L]

end KummerTwistLemmas

end CrystallineSemistableComparison
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.RootLoc
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial

namespace CrystallineSemistableComparison.KummerTwistLemmas

open GlobalTheory.EtC

theorem cyc_pow (p b : ℕ) (hp : p.Prime) (hb : 0 < b) :
    ∀ a : ℕ, expand ℤ (p ^ a) (cyclotomic (p ^ b) ℤ) = cyclotomic (p ^ (a + b)) ℤ
  | 0 => by simp
  | a + 1 => by
    rw [pow_succ', expand_mul, cyc_pow p b hp hb a,
      cyclotomic_expand_eq_cyclotomic hp (dvd_pow_self p (by omega : a + b ≠ 0))]
    congr 1
    rw [← pow_succ]
    congr 1
    omega

theorem rootLoc (p a b : ℕ) [Fact p.Prime] (hb : 0 < b) (U : Scheme.{0}) (ξ : Prim (p ^ b) Γ(U, ⊤)) :
    Loc U fun V g => ∃ ζ : Prim (p ^ (a + b)) Γ(V, ⊤), ζ.1 ^ (p ^ a) = g.appTop.hom ξ.1 := by
  have hp : p.Prime := Fact.out
  have hpU : IsUnit (p : Γ(U, ⊤)) := by
    have h := ξ.2.1
    rw [Nat.cast_pow] at h
    exact (isUnit_pow_iff hb.ne').1 h
  have hξ1 : ξ.1 ^ (p ^ b) = 1 := by
    obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one (p ^ b) ℤ
    have := congrArg (aeval ξ.1) hh
    rw [map_mul, ξ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at this
    exact this
  have hξu : IsUnit ξ.1 := by
    refine isUnit_iff_exists_inv.2 ⟨ξ.1 ^ (p ^ b - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero)), hξ1]
  obtain ⟨S, hS, hP⟩ := kumLoc U (p ^ a) hξu.unit (by rw [Nat.cast_pow]; exact hpU.pow _)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨v, hv⟩ := hP V g hg
  rw [IsUnit.unit_spec] at hv
  have hpV : IsUnit (p : Γ(V, ⊤)) := by simpa using hpU.map g.appTop.hom
  refine ⟨⟨v, by rw [Nat.cast_pow]; exact hpV.pow _, ?_⟩, hv⟩
  rw [← cyc_pow p b hp hb a, expand_aeval, hv]
  exact (Prim.map g.appTop.hom ξ).2.2

end CrystallineSemistableComparison.KummerTwistLemmas
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSectionLemmas
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.SheafSectionLemmas

open GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hSP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  refine ⟨Sieve.bind S.arrows (fun V g hg => (h' V g (hSP V g hg)).choose),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => (h' V g (hSP V g hg)).choose_spec.1), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact (h' V g (hSP V g hg)).choose_spec.2 W k hk

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem isSheaf_types (G : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (G.obj ⋙ forget _) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 G.property)

theorem sec_eq_of_loc {F : Shv R} {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ((isSheaf_types F) S hS).isSeparatedFor.ext fun _ g hg => hSP _ g hg

theorem sec_subsingleton_of_isEmpty (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ⟨fun a b => ((isSheaf_types F).isSheafFor (⊥ : Presieve U)
    (by rw [Sieve.generate_bot]; exact Scheme.bot_mem_grothendieckTopology U)).isSeparatedFor.ext (fun _ _ h => h.elim)⟩

theorem epi_of_loc {F G : Shv R} (φ : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec G U), Loc U fun V g => ∃ x : Sec F V, Sec.map φ x = Sec.res g y) : Epi φ := by
  have : Sheaf.IsLocallySurjective φ := by
    constructor
    intro U y
    obtain ⟨S, hS, hSP⟩ := h U y
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    obtain ⟨x, hx⟩ := hSP V g hg
    exact ⟨x, hx⟩
  infer_instance

theorem sec_map_comp {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem sec_map_injective_of_mono {X Y : Shv R} (f : X ⟶ Y) [Mono f] (U : Scheme.{0}) :
    Function.Injective (Sec.map f (U := U)) := by
  have h1 : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have h2 : Mono (f.hom.app (op U)) := (NatTrans.mono_iff_mono_app f.hom).1 h1 (op U)
  exact (ModuleCat.mono_iff_injective _).1 h2

theorem epi_lift_of_loc {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : ∀ (U : Scheme.{0}) (y : Sec Y U), Sec.map g y = 0 →
      Loc U fun V k => ∃ x : Sec X V, Sec.map f x = Sec.res k y) :
    Epi (kernel.lift g f w) := by
  apply epi_of_loc
  intro U y
  have hy : Sec.map g (Sec.map (kernel.ι g) y) = 0 := by
    rw [← sec_map_comp, kernel.condition]; rfl
  refine loc_mono (h U _ hy) fun V k ⟨x, hx⟩ => ⟨x, ?_⟩
  apply sec_map_injective_of_mono (kernel.ι g)
  rw [← sec_map_comp, kernel.lift_ι, hx, GlobalTheory.EtC.CupSpec.map_res]

theorem ker_comp_zero {X Y Z : Shv R} (f : X ⟶ Y) (g : X ⟶ Z)
    (h : ∀ (U : Scheme.{0}) (y : Sec X U), Sec.map f y = 0 → Sec.map g y = 0) : kernel.ι f ≫ g = 0 := by
  apply Sheaf.hom_ext
  ext U y
  refine (h U.unop (Sec.map (kernel.ι f) y) ?_).trans rfl
  rw [← sec_map_comp, kernel.condition]; rfl

end CrystallineSemistableComparison.SheafSectionLemmas
end
end

