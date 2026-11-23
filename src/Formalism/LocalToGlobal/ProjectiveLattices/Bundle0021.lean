module

public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def incl : M →ₗ[K] L ⊗[K] M := TensorProduct.mk K L M 1

end Ext

section Forms

variable {K : Type} [Field K] {LL : Type} [Field LL] [NumberField LL] [Algebra K LL]
variable {C : Type} [AddCommGroup C] [Module K C] {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {D : D7}

def rhoOf (LL : Type) [Field LL] [Algebra K LL] {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) :
    G0 →* (LL ⊗[K] C →ₗ[LL] LL ⊗[K] C) where
  toFun g := (ρC g).baseChange LL
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g g' := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

end Forms

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
section
noncomputable section

namespace Formalism.L2.Pj.CompSplitPfB

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem cspB_over {S : Type} [CommRing S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) :
    x ≫ Xo.s = spMap (algebraMap c.F S) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
  rw [hx, sOf, ← Spec.map_comp]
  rfl

def cspB_lift {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    Sp S ⟶ Xo.XF c :=
  pullback.lift x (spMap (algebraMap c.F S)) (cspB_over hx)

theorem cspB_lift_fst {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    cspB_lift x hx ≫ pullback.fst _ _ = x := by
  unfold cspB_lift
  exact pullback.lift_fst _ _ _

theorem cspB_lift_snd {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    cspB_lift x hx ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  unfold cspB_lift
  exact pullback.lift_snd _ _ _

theorem cspB_lift_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) {z : Sp T ⟶ Xo.X} (hz : z ≫ Xo.s = sOf c T)
    (hzx : z = spMap φ.toRingHom ≫ x) : cspB_lift z hz = spMap φ.toRingHom ≫ cspB_lift x hx := by
  apply pullback.hom_ext
  · rw [cspB_lift_fst, Category.assoc, cspB_lift_fst, hzx]
  · rw [cspB_lift_snd, Category.assoc, cspB_lift_snd, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (AlgHom.comp_algebraMap φ).symm

theorem cspB_idem_eq_of {S : Type} [CommRing S] {a b : S} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : ∀ q : PrimeSpectrum S, a ∉ q.asIdeal ↔ b ∉ q.asIdeal) : a = b := by
  have key : ∀ x y : S, IsIdempotentElem x → IsIdempotentElem y →
      (∀ q : PrimeSpectrum S, x ∉ q.asIdeal → y ∉ q.asIdeal) → x = x * y := by
    intro x y hx hy hxy
    have hid : x * (1 - y) * (x * (1 - y)) = x * (1 - y) := by
      linear_combination (1 - y) ^ 2 * hx.eq + x * hy.eq
    have hmem : x * (1 - y) ∈ nilradical S := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      intro J hJ
      by_cases hxJ : x ∈ J
      · exact J.mul_mem_right _ hxJ
      · have hyJ : y ∉ J := hxy ⟨J, hJ⟩ hxJ
        apply J.mul_mem_left
        have h0 : y * (1 - y) = 0 := by linear_combination -hy.eq
        have h1 : y * (1 - y) ∈ J := by rw [h0]; exact J.zero_mem
        exact (hJ.mem_or_mem h1).resolve_left hyJ
    obtain ⟨n, hn⟩ := mem_nilradical.mp hmem
    have hpow : ∀ k : ℕ, (x * (1 - y)) ^ (k + 1) = x * (1 - y) := by
      intro k
      induction k with
      | zero => rw [zero_add, pow_one]
      | succ k ih => rw [pow_succ, ih, hid]
    have h0 : x * (1 - y) = 0 := by rw [← hpow n, pow_succ, hn, zero_mul]
    linear_combination h0
  calc a = a * b := key a b ha hb (fun q h => (hab q).mp h)
    _ = b * a := mul_comm a b
    _ = b := (key b a hb ha (fun q h => (hab q).mpr h)).symm

variable (C : Set (Xo.XF c)) (hC : IsClopen C)

def cspB_idem {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) : S :=
  ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm
    ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩).1

theorem cspB_idem_idem {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    IsIdempotentElem (cspB_idem C hC x hx) := by
  unfold cspB_idem
  exact ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm _).2

theorem cspB_idem_spec {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S)
    (q : PrimeSpectrum S) : cspB_idem C hC x hx ∉ q.asIdeal ↔ cspB_lift x hx q ∈ C := by
  have h1 := (PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).apply_symm_apply
    ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩
  have h2 : q ∈ ((((PrimeSpectrum.isIdempotentElemEquivClopens (R := S))
      ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm
        ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩)) :
          TopologicalSpace.Clopens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) ↔
      q ∈ (cspB_lift x hx) ⁻¹' C := by
    rw [h1]
    rfl
  exact h2

theorem cspB_idem_congr {S : Type} [CommRing S] [Algebra c.F S] {x x' : Sp S ⟶ Xo.X}
    (hx : x ≫ Xo.s = sOf c S) (hx' : x' ≫ Xo.s = sOf c S) (h : x' = x) :
    cspB_idem C hC x' hx' = cspB_idem C hC x hx := by
  subst h
  rfl

theorem cspB_idem_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) {z : Sp T ⟶ Xo.X} (hz : z ≫ Xo.s = sOf c T)
    (hzx : z = spMap φ.toRingHom ≫ x) : φ (cspB_idem C hC x hx) = cspB_idem C hC z hz := by
  apply cspB_idem_eq_of ((cspB_idem_idem C hC x hx).map φ) (cspB_idem_idem C hC z hz)
  intro q
  rw [cspB_idem_spec C hC z hz q, cspB_lift_map φ hx hz hzx]
  exact cspB_idem_spec C hC x hx (PrimeSpectrum.comap φ.toRingHom q)


variable (Xo c) in
def cspB_rule : Rul Xo c := fun _ y => cspB_idem C hC y.x y.x_over

theorem cspB_rule_natural : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (cspB_rule Xo c C hC) := by
  intro p q φ y z hyz
  first
  | exact cspB_idem_map C hC φ y.x_over z.x_over hyz.1
  | exact (cspB_idem_map C hC φ y.x_over z.x_over hyz.1).symm

theorem cspB_rule_bor (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R) (hb : FrBor t y y') :
    cspB_rule Xo c C hC p y' = cspB_rule Xo c C hC p y := by
  exact cspB_idem_congr C hC y.x_over y'.x_over hb.1

theorem cspB_evR {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    evR Xo c (cspB_rule Xo c C hC) y = cspB_idem C hC y.x y.x_over := by
  unfold evR evalAt
  rw [dite_eq_left hy]
  first
  | exact cspB_idem_map C hC _ _ _ hy.choose_spec.choose_spec.choose_spec.1
  | exact cspB_idem_map C hC _ _ _ hy.choose_spec.choose_spec.choose_spec.1.1

theorem cspB_evR_zero {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (hy : ¬ FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (f : Rul Xo c) :
    evR Xo c f y = 0 := by
  unfold evR evalAt
  rw [dite_eq_right hy]

theorem cspB_evR_mul {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (f g : Rul Xo c) :
    evR Xo c (f * g) y = evR Xo c f y * evR Xo c g y := by
  exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g y

theorem cspB_genPt_mem (Z : Comp Xo c) : genPt Z ∈ (Z : Set (Xo.XF c)) := by
  unfold genPt
  have hcl : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
  have hS : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  have hg : IsGenericPoint hS.genericPoint (closure (Z : Set (Xo.XF c))) := by
    first
    | exact hS.isGenericPoint_genericPoint_closure
    | exact hS.genericPoint_spec
  rw [hcl.closure_eq] at hg
  exact hg.mem

theorem cspB_isClopen (hdisj : ∀ Z Z' : Comp Xo c, Z ≠ Z' → Disjoint (Z : Set (Xo.XF c)) Z')
    (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := CompFin.finite_comp Xo c
  refine ⟨isClosed_of_mem_irreducibleComponents _ Z.2, ?_⟩
  have hU : (Z : Set (Xo.XF c)) = (⋃ Z' : {Z' : Comp Xo c // Z' ≠ Z}, (Z'.1 : Set (Xo.XF c)))ᶜ := by
    ext p
    constructor
    · intro hp hp'
      obtain ⟨⟨Z', hne⟩, hZ'⟩ := Set.mem_iUnion.1 hp'
      exact Set.disjoint_left.1 (hdisj Z Z' (Ne.symm hne)) hp hZ'
    · intro hp
      have hall : p ∈ ⋃₀ irreducibleComponents (Xo.XF c) := by
        rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨W, hW, hpW⟩ := Set.mem_sUnion.1 hall
      by_contra hpZ
      refine hp (Set.mem_iUnion.2 ⟨⟨⟨W, hW⟩, fun hWZ => hpZ ?_⟩, hpW⟩)
      rw [← hWZ]
      exact hpW
  rw [hU]
  exact (isClosed_iUnion_of_finite fun Z' : {Z' : Comp Xo c // Z' ≠ Z} =>
    isClosed_of_mem_irreducibleComponents _ Z'.1.2).isOpen_compl



end Formalism.L2.Pj.CompSplitPfB
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def lamOf (la : HeightOneSpectrum (𝓞 c.F)) : PointsOfFlagModel.abelian₂ (Formalism.MainNotions.WeightAlgebra.resCh la) c :=
  ⟨la, by
    have h : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F ⧸ la.asIdeal) = 0 := by
      unfold Formalism.MainNotions.WeightAlgebra.resCh
      exact CharP.cast_eq_zero _ _
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa using h)⟩

def LiesOverBaseChange (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (η : PointsOfFlagModel.Pt Tw .yy) : Prop :=
  letI := io.toAlgebra
  η.1 = lamOf la ∧ ∃ eF : T.Fr →+* ↥η.2.1.S,
    eF.comp io = η.2.2.1.fK ∧
    (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧
    (∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧
    η.2.2.1.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x ∧
    ∀ τ i, ∃ u' : Sp (DualNumber ↥η.2.1.S) ⟶ (Tw.Y η.1).oF.t.G.left,
      u' ≫ (Tw.Y η.1).m.φ = (η.2.2.2.u τ i).left ∧
      u' ≫ (Tw.Y η.1).m0.toSABMap.φ = spMap (dualMap eF) ≫ y.1.u τ i

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  sec Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laU (U σ) a n)).comap (rdU (U σ))

theorem cusp_le_sec (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n ≤ sec Xo c a n := inf_le_left

theorem mem_cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    f ∈ cusp Xo c U a n ↔ f ∈ sec Xo c a n ∧ ∀ σ : c.F →+* ℂ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) := by
  unfold cusp
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]

def mulC (f g : Rul Xo c) : Rul Xo c := f * g

theorem mulC_mem_sec (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : mulC Xo c f g ∈ sec Xo c (a + a') (n + n') := by
  unfold mulC
  exact sec_mul Xo c a a' n n' hf hg

def CuspMul : Prop :=
  ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), Dom a n → Dom a' n' → f ∈ cusp Xo c U a n →
    g ∈ cusp Xo c U a' n' → mulC Xo c f g ∈ cusp Xo c U (a + a') (n + n')

set_option maxSynthPendingDepth 1 in
def CuspFD : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)

def algCls (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop := y.IsAlg

def valSet (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  Set.range (vAtV : PtV Xo c cls Unit (fun _ _ _ _ => True) la → Rul Xo c → EReal)

variable {Xo c cls}

theorem isVal_vAt {PY : Type} {lies : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) : IsVal la (vAtV y) :=
  ⟨vAtV_zero y, vAtV_ne_bot y, vAtV_add y, fun a f ha => vAtV_smul y a f ha, vAtV_mul y⟩

theorem isVal_valSet (la : HeightOneSpectrum (𝓞 c.F)) : ∀ v ∈ valSet Xo c cls la, IsVal la v := by
  rintro _ ⟨y, rfl⟩
  exact isVal_vAt y

variable (Xo c cls)

def LiesTotal (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ la (T : CDVR) (ι : c.F →+* T.Fr) (e : ℕ), OverLa la T.V ι e → ∀ y : IntFr Xo c T ι, cls T ι y →
    ∃ η, lies la T ι y η

variable {Xo c cls}

theorem nonneg_iff_of_liesTotal {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (h : LiesTotal Xo c cls PY lies) (f : Rul Xo c) :
    (∀ la, ∀ v ∈ valSet Xo c cls la, 0 ≤ v f) ↔
      ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f := by
  constructor
  · rintro h0 la ⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩
    exact h0 la _ ⟨PtV.mk la ho y hy () trivial, rfl⟩
  · rintro h0 la _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    obtain ⟨η', hη'⟩ := h la T ι e ho y hy
    exact h0 la (PtV.mk la ho y hy η' hη')

end Formalism.L2.Pj
end
end

