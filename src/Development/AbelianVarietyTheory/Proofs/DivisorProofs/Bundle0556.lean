module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualConvPowPrimePowApplyPow
section
open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem convPow_prime_apply_pow_prime (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p) (a ^ p) = χ (mulBy R (G.A n) p a) ^ p := by
  let A := G.A n
  let S := ULift.{0} R
  let σ : R →+* S := ULift.ringEquiv.symm.toRingHom.comp (frobRing h)
  let : Algebra R S := σ.toAlgebra
  let : Module R S := Algebra.toModule
  let : SMul R S := Algebra.toSMul
  have hA : (p : A) = 0 := natCast_eq_zero_of_algebra h A
  -- With Frobenius acting on the target scalars, precomposition by the pth power is linear.
  let pullPow (φ : CartierDual R A) : WithConv (A →ₗ[R] S) := toConv
    { toFun := fun x => ULift.up (φ (x ^ p))
      map_add' := fun x y => by
        change ULift.up (φ.ofConv ((x + y) ^ p)) =
          ULift.up (φ.ofConv (x ^ p) + φ.ofConv (y ^ p))
        rw [← frobRing_apply hA (x + y), map_add, map_add, frobRing_apply, frobRing_apply]
      map_smul' := fun r x => by
        change ULift.up (φ.ofConv ((r • x) ^ p)) = r • ULift.up (φ.ofConv (x ^ p))
        rw [smul_pow, φ.ofConv.map_smul, Algebra.smul_def (R := R) (A := S)]
        change ULift.up (r ^ p * φ.ofConv (x ^ p)) =
          ULift.up (frobRing h r * φ.ofConv (x ^ p))
        rw [frobRing_apply] }
  let pull : CartierDual R A →* WithConv (A →ₗ[R] S) :=
    { toFun := pullPow
      map_one' := WithConv.ext (LinearMap.ext fun x => by
        change ULift.up ((1 : CartierDual R A) (x ^ p)) = (1 : WithConv (A →ₗ[R] S)) x
        rw [LinearMap.convOne_apply, LinearMap.convOne_apply, counit_pow]
        change ULift.up (counit (R := R) x ^ p) = ULift.up (frobRing h (counit x))
        rw [frobRing_apply])
      map_mul' := fun φ ψ => WithConv.ext (LinearMap.ext fun x => by
        let d := Coalgebra.Repr.arbitrary R x
        let dPow : Coalgebra.Repr R (x ^ p) (A × A) :=
          ⟨d.index, fun i => d.left i ^ p, fun i => d.right i ^ p, by
            rw [comul_pow, ← d.eq,
              ← frobRing_apply (natCast_eq_zero_of_algebra h (A ⊗[R] A)), map_sum]
            simp only [frobRing_apply, Algebra.TensorProduct.tmul_pow]⟩
        change ULift.up ((φ * ψ) (x ^ p)) = (pullPow φ * pullPow ψ) x
        rw [dPow.convMul_apply, d.convMul_apply]
        exact map_sum ULift.ringEquiv.symm (fun i => φ (d.left i ^ p) * ψ (d.right i ^ p)) d.index) }
  obtain ⟨s, hs⟩ := exists_dualSystem R A
  have hmul : mulBy R A p a = ∑ i ∈ s, (i.1 ^ p) a • i.2 ^ p := by
    have he := BialgHom.toLinearMap_convPow (toConv (BialgHom.id R A)) p
    exact (congrArg (fun f : WithConv (A →ₗ[R] A) => f a) he).trans
      (convPow_prime_apply h s Prod.fst Prod.snd LinearMap.id (fun x => (hs x).symm) a)
  let f := (pull χ).ofConv
  have hf (x : A) : f x = ∑ i ∈ s, i.1 x • f i.2 := by
    simpa only [map_sum, map_smul] using congrArg f (hs x).symm
  let g : A →ₗ[R] S := (Algebra.linearMap R S).comp χ.ofConv
  have hg (x : A) : f x ^ p = g (x ^ p) := by
    change ULift.up (χ (x ^ p) ^ p) = ULift.up (frobRing h (χ (x ^ p)))
    rw [frobRing_apply]
  have e : pull (χ ^ p) a = g (mulBy R A p a) := by
    rw [map_pow]
    change (toConv f ^ p) a = _
    rw [convPow_prime_apply h s Prod.fst (fun i => f i.2) f hf a, hmul, map_sum]
    simp only [map_smul, hg]
  exact (congrArg ULift.down e).trans (frobRing_apply h _)

theorem convPow_primePow_apply_pow (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  induction r generalizing a with
  | zero =>
    simp only [pow_zero, pow_one]
    rw [mulBy, pow_one]
    rfl
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, convPow_prime_apply_pow_prime p R h G n, map_pow, ih,
      mulBy_mulBy, ← pow_mul, mul_comm (p ^ r) p, ← pow_succ']

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainCoboundaryExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem cechOneCochainToPosetCochain_coboundary_exists : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R)
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  intro I _ X R _ s U hU hinf c hc
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun T => (cv s U hU hinf T).symm (rsT (b T.unop.pt) (cap U T.unop)), ?_⟩
  funext T T' φ
  apply (cv s U hU hinf T').injective
  have hTT' : cap U T'.unop ≤ cap U T.unop := cap_mono U (leOfHom φ.unop)
  have hp : cap U T.unop ≤ U T.unop.pt := cap_le U T.unop.pt_mem
  have hp' : cap U T'.unop ≤ U T'.unop.pt := cap_le U T'.unop.pt_mem
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (hTT'.trans hp) hp'
  rw [amitsur_d0_apply, map_sub, cv_mp, cv_toPos, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hb,
    GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT inf_le_right hle, GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_rsT hp hTT']

end GlobalTheory.CechCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainMemCocycles
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem cechOneCochainToPosetCochain_mem_cocycles : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by
  intro I _ X R _ s U hU hinf c hc T T' T'' φ ψ
  have h1 : T.unop.set ⊆ T'.unop.set := NE.le_iff.1 (leOfHom φ.unop)
  have h2 : T'.unop.set ⊆ T''.unop.set := NE.le_iff.1 (leOfHom ψ.unop)
  have ha : T.unop.pt ∈ T''.unop.set := h2 (h1 T.unop.pt_mem)
  have hb : T'.unop.pt ∈ T''.unop.set := h2 T'.unop.pt_mem
  have ha' : T.unop.pt ∈ T'.unop.set := h1 T.unop.pt_mem
  have hW : cap U T''.unop ≤ U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt :=
    le_inf (le_inf (cap_le U ha) (cap_le U hb)) (cap_le U T''.unop.pt_mem)
  have hT' : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (cap_le U ha') (cap_le U T'.unop.pt_mem)
  have h23 : cap U T''.unop ≤ cap U T'.unop := cap_mono U (leOfHom ψ.unop)
  have key := congrArg (fun x => rsT x (cap U T''.unop)) (hc T.unop.pt T'.unop.pt T''.unop.pt)
  simp only [GlobalTheory.KS.rsT_add] at key
  have e1 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T.unop.pt ⊓ U T'.unop.pt := inf_le_left
  have e2 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T'.unop.pt ⊓ U T''.unop.pt :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e3 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T.unop.pt ⊓ U T''.unop.pt :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [GlobalTheory.KS.rsT_rsT e1 hW, GlobalTheory.KS.rsT_rsT e2 hW, GlobalTheory.KS.rsT_rsT e3 hW] at key
  apply (cv s U hU hinf T'').injective
  rw [map_add (f := _), cv_toPos, cv_mp, cv_toPos, cv_toPos, GlobalTheory.KS.rsT_rsT hT' h23]
  exact key.symm

end GlobalTheory.CechCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechToPosetPosetToCechSubCoboundary
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechCmp

theorem cechToPoset_posetToCech_sub_coboundary : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R]
    (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) →
      ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf (toCech s U hU hinf f) - f := by
  intro I _ X R _ s U hU hinf f hf
  have hm : ∀ {S T : NE I}, S.set ⊆ T.set → ((op S : (NE I)ᵒᵖ) ⟶ op T) :=
    fun h => (homOfLE (NE.le_iff.2 h)).op
  have hsg : ∀ T : NE I, (NE.single T.pt).set ⊆ T.set := fun T => by
    rw [NE.set_single]; exact Set.singleton_subset_iff.2 T.pt_mem
  have sub : ∀ {S T : (NE I)ᵒᵖ} (u v : S ⟶ T), u = v := fun u v =>
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  refine ⟨fun T => -f (op (NE.single T.unop.pt)) T (hm (hsg T.unop)), ?_⟩
  funext T T' φ
  have hTT : T.unop.set ⊆ T'.unop.set := NE.le_iff.1 (leOfHom φ.unop)
  have ha' : T.unop.pt ∈ T'.unop.set := hTT T.unop.pt_mem
  have hab : (NE.pair T.unop.pt T'.unop.pt).set ⊆ T'.unop.set := by
    rw [NE.set_pair]; exact Set.insert_subset ha' (Set.singleton_subset_iff.2 T'.unop.pt_mem)
  let χ : op (NE.pair T.unop.pt T'.unop.pt) ⟶ T' := hm hab
  let ψa : op (NE.single T.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt) :=
    (homOfLE (NE.pair_le_single_left T.unop.pt T'.unop.pt)).op
  let ψb : op (NE.single T'.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt) :=
    (homOfLE (NE.pair_le_single_right T.unop.pt T'.unop.pt)).op
  have c1 := Z1.comp ⟨f, hf⟩ (hm (hsg T.unop)) φ
  have c2 := Z1.comp ⟨f, hf⟩ ψa χ
  have c3 := Z1.comp ⟨f, hf⟩ ψb χ
  rw [sub (hm (hsg T.unop) ≫ φ) (ψa ≫ χ)] at c1
  have e3 : (hm (hsg T'.unop) : op (NE.single T'.unop.pt) ⟶ T') = ψb ≫ χ := sub _ _
  have key : toPos s U hU hinf (toCech s U hU hinf f) T T' φ =
      mp (capF s U hU hinf) χ (f _ _ ψa) - mp (capF s U hU hinf) χ (f _ _ ψb) := by
    apply (cv s U hU hinf T').injective
    have h1 : U T.unop.pt ⊓ U T'.unop.pt ≤ cap U (NE.pair T.unop.pt T'.unop.pt) :=
      (cap_pair U _ _).ge
    have h2 : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt :=
      le_inf (cap_le U ha') (cap_le U T'.unop.pt_mem)
    rw [cv_toPos, toCech_apply, map_sub, cv_mp, cv_mp, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT h1 h2,
      GlobalTheory.KS.rsT_rsT h1 h2]
  simp only [amitsur_d0_apply, Pi.sub_apply, map_neg, key]
  rw [e3]
  simp only at c1 c2 c3
  linear_combination -c3 + c2 - c1

end GlobalTheory.CechCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeGlueLocalCondition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ClosedGlue
open Scheme TopologicalSpace

theorem restrict_app_eq_zero_iff {T S : Scheme.{0}} (f : T ⟶ S) (U : S.Opens) (V : U.toScheme.Opens)
    (a : Γ(S, U.ι ''ᵁ V)) : ((f ∣_ U).app V).hom a = 0 ↔ (f.app (U.ι ''ᵁ V)).hom a = 0 := by
  rw [morphismRestrict_app]
  exact map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1

def killIdeal {S : Scheme.{0}} (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) (W : S.Opens) :
    Ideal Γ(S, W) :=
  ⨅ (T : Scheme.{0}) (t : T ⟶ S) (_ : Φ T t), RingHom.ker (t.app W).hom

theorem mem_killIdeal {S : Scheme.{0}} (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) {W : S.Opens}
    {b : Γ(S, W)} :
    b ∈ killIdeal Φ W ↔ ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app W).hom b = 0 := by
  simp [killIdeal, Submodule.mem_iInf, RingHom.mem_ker]

theorem app_res_eq_zero {S T : Scheme.{0}} (t : T ⟶ S) {V W : S.Opens} (h : V ≤ W) (b : Γ(S, W))
    (hb : (t.app W).hom b = 0) : (t.app V).hom ((S.presheaf.map (homOfLE h).op).hom b) = 0 := by
  have e := congrArg (fun φ => φ.hom b) (t.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e, hb, map_zero]

theorem killIdeal_map_basicOpen {S : Scheme.{0}} (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop)
    (hstab : ∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t))
    (hcov : ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t)
    (W : S.affineOpens) (f : Γ(S, W)) :
    (killIdeal Φ W).map (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom =
      killIdeal Φ (S.basicOpen f) := by
  have inst := W.2.isLocalization_basicOpen f
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, mem_killIdeal]
    intro T t ht
    exact app_res_eq_zero t _ b ((mem_killIdeal Φ).1 hb T t ht)
  · intro a ha
    obtain ⟨c, m, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) a
    have hc : algebraMap Γ(S, W) Γ(S, S.basicOpen f) c ∈ killIdeal Φ (S.basicOpen f) := by
      rw [← IsLocalization.mk'_spec Γ(S, S.basicOpen f) c m]
      exact Ideal.mul_mem_right _ _ ha
    obtain ⟨n, hn⟩ := _root_.GlobalTheory.pow_kills_on_compact_of_local S Φ (W : S.Opens) W.2.isCompact f c (fun y hy => by
      obtain ⟨U, Z, i, hyU, hi, hrep⟩ := hcov y
      exact _root_.GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented S Φ hstab U Z i hi hrep (W : S.Opens) f c
        (fun T t ht => (mem_killIdeal Φ).1 hc T t ht) y hyU hy)
    change IsLocalization.mk' _ c _ ∈ Ideal.map (algebraMap Γ(S, W) Γ(S, S.basicOpen f)) _
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨f ^ n, ⟨n, rfl⟩, (mem_killIdeal Φ).2 hn⟩

end GlobalTheory.ClosedGlue


open GlobalTheory.ClosedGlue in
theorem GlobalTheory.closedSubscheme_glue : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → (∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ Φ V (V.ι ≫ t)) → Φ T t) → (∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  intro S Φ hstab hloc hcov
  let J : S.IdealSheafData :=
    { ideal := fun W => killIdeal Φ W
      map_ideal_basicOpen := fun W f => killIdeal_map_basicOpen Φ hstab hcov W f }
  have hfac : ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t →
      ∃ z : T ⟶ J.subscheme, z ≫ J.subschemeι = t := by
    intro T t ht
    have hle : J ≤ t.ker := by
      refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
      intro W b hb
      exact (mem_killIdeal Φ).1 hb T t ht
    exact ⟨t.toImage ≫ Scheme.IdealSheafData.inclusion hle, by simp⟩
  have hZ : Φ J.subscheme J.subschemeι := by
    apply hloc
    intro τ
    obtain ⟨U, Z, i, hxU, hi, hrep⟩ := hcov (J.subschemeι τ)
    refine ⟨J.subschemeι ⁻¹ᵁ U, hxU, ?_⟩
    rw [← morphismRestrict_ι]
    refine (hrep _ _).2 ⟨IsClosedImmersion.lift i (J.subschemeι ∣_ U) ?_,
      IsClosedImmersion.lift_fac _ _ _⟩
    refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
    intro W a ha
    rw [Scheme.Hom.ker_apply] at ha
    rw [RingHom.mem_ker]
    refine (restrict_app_eq_zero_iff _ U W a).2 ?_
    have hmem : a ∈ killIdeal Φ (U.ι ''ᵁ W) := (mem_killIdeal Φ).2 fun T t ht => by
      obtain ⟨z, hz⟩ := (hrep _ (t ∣_ U)).1 (by rw [morphismRestrict_ι]; exact hstab _ _ _ _ ht)
      refine (restrict_app_eq_zero_iff t U W a).1 ?_
      rw [← hz]
      show (z.app (i ⁻¹ᵁ W)).hom ((i.app W).hom a) = 0
      rw [RingHom.mem_ker.1 ha, map_zero]
    have h2 := (J.ker_subschemeι_app ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion _⟩).ge hmem
    exact h2
  refine ⟨J.subscheme, J.subschemeι, inferInstance, fun T t => ⟨hfac T t, ?_⟩⟩
  rintro ⟨z, rfl⟩
  exact hstab _ _ _ _ hZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneAdditiveFormalGroupLawXPow
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem coboundaryOne_additiveFormalGroupLaw_X_pow (R : Type) [CommRing R] (d N : ℕ) (m : Fin d) (hN : 1 ≤ N) :
    cob1 (addLaw R d) (X m ^ N) = ∑ i ∈ Finset.Ioo 0 N,
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
  have h1 : HasSubst (addLaw R d) := hasSubst_of_constantCoeff_zero fun i => by simp [addLaw]
  have h2 : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have h3 : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold cob1 inL inR
  rw [subst_pow h1, subst_pow h2, subst_pow h3, subst_X h1, subst_X h2, subst_X h3]
  simp only [addLaw]
  have hr : Finset.range (N + 1) = insert 0 (insert N (Finset.Ioo 0 N)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [add_pow, hr, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
  simp only [pow_zero, Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, mul_one, one_mul]
  have key : ∀ i ∈ Finset.Ioo 0 N,
      (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R) ^ i * X (Sum.inr m) ^ (N - i) *
        (N.choose i : MvPowerSeries (Fin d ⊕ Fin d) R) =
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
    intro i _
    rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, ← nsmul_eq_mul', ← map_nsmul,
      nsmul_one]
  rw [Finset.sum_congr rfl key]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCoboundaryOneAdditiveEqZeroOfDegree
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

private theorem homog_one {R τ : Type} [CommRing R] : (1 : MvPowerSeries τ R).IsHomogeneous 0 := by
  classical
  intro γ h
  rw [coeff_one] at h
  by_cases h0 : γ = 0
  · simp [h0]
  · simp [h0] at h

private theorem homog_X {R τ : Type} [CommRing R] (t : τ) :
    (X t : MvPowerSeries τ R).IsHomogeneous 1 := by
  classical
  intro γ h
  rw [coeff_X] at h
  by_cases h0 : γ = Finsupp.single t 1
  · simp [h0, Finsupp.weight_single]
  · simp [h0] at h

private theorem homog_pow {R τ : Type} [CommRing R] {f : MvPowerSeries τ R}
    (hf : f.IsHomogeneous 1) (n : ℕ) : (f ^ n).IsHomogeneous n := by
  induction n with
  | zero => rw [pow_zero]; exact homog_one
  | succ n ih => rw [pow_succ]; exact IsHomogeneous.mul (f := f ^ n) (g := f) ih hf

private theorem homog_prod {R σ τ : Type} [CommRing R] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, (a i).IsHomogeneous 1) (n : σ → ℕ) (s : Finset σ) :
    (∏ i ∈ s, a i ^ n i).IsHomogeneous (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact homog_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]; exact IsHomogeneous.mul (f := a i ^ n i) (p := n i) (homog_pow (ha i) (n i)) ih

theorem coeff_subst_linear_eq_zero_of_degree {R σ τ : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, (a i).IsHomogeneous 1) {N : ℕ}
    {b : MvPowerSeries σ R} (hb : ∀ α : σ →₀ ℕ, α.degree = N → coeff α b = 0)
    {γ : τ →₀ ℕ} (hγ : γ.degree = N) : coeff γ (subst a b) = 0 := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact IsHomogeneous.coeff_eq_zero (f := a i) (p := 1) (ha i) (by simp)
  rw [coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun α => ?_
  by_cases h : α.degree = N
  · rw [hb α h, zero_smul]
  · have := IsHomogeneous.coeff_eq_zero (f := ∏ i ∈ α.support, a i ^ α i)
      (p := ∑ i ∈ α.support, α i) (homog_prod ha α α.support) (d := γ) (by
      rw [hγ]; exact fun h' => h h'.symm)
    rw [Finsupp.prod, this, smul_zero]

theorem coeff_cob1_addLaw_eq_zero_of_degree_eq : ∀ (R : Type) [CommRing R] (d N : ℕ)
    (b : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree = N → coeff α b = 0) →
    ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → coeff γ (cob1 (addLaw R d) b) = 0 := by
  intro R _ d N b hb γ hγ
  unfold cob1 inL inR
  rw [map_sub, map_sub,
    coeff_subst_linear_eq_zero_of_degree (a := addLaw R d)
      (fun i => IsHomogeneous.add (p := 1) (homog_X (Sum.inl i)) (homog_X (Sum.inr i))) hb hγ,
    coeff_subst_linear_eq_zero_of_degree (fun i => homog_X _) hb hγ,
    coeff_subst_linear_eq_zero_of_degree (fun i => homog_X _) hb hγ]
  simp

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenEqBotOfRootInUnipotentRadicalStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coindEigen_eq_bot_of_root_in_unipotent_radical : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → ψ ≠ 1 → ∀ a c : Fin r, cutEdge j a c → b (w a) < b (w c) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = ⊥ := by
  first | exact @GlobalTheory.FinGL.MackeyRadical.eig_eq_bot_of_radical | exact GlobalTheory.FinGL.MackeyRadical.eig_eq_bot_of_radical | (intros; apply GlobalTheory.FinGL.MackeyRadical.eig_eq_bot_of_radical <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenSortingPermEqLeviWhittakerStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coindEigen_sorting_perm_eq_levi_whittaker : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → (∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c) → (∀ a e c : Fin r, a ≤ e → e ≤ c → b (w a) = b (w c) → b (w e) = b (w a)) → (∀ a c : Fin r, cutEdge j a c → b (w c) ≤ b (w a)) → (∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = eig σ {p | (p : GL (Fin r) F) ∈ unip F r} (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) := by
  first | exact @GlobalTheory.FinGL.SortWh.eig_conj_eq_leviWh | exact GlobalTheory.FinGL.SortWh.eig_conj_eq_leviWh | (intros; apply GlobalTheory.FinGL.SortWh.eig_conj_eq_leviWh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleExcisionVanishingUnderRefinementStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleExcision_vanishing_under_refinement : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  first | (exact @GlobalTheory.EtC.mvRefine_main) | (exact GlobalTheory.EtC.mvRefine_main) | (intros; apply GlobalTheory.EtC.mvRefine_main <;> assumption)
end

