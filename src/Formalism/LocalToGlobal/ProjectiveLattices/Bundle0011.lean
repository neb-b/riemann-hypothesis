module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CompFin
section
noncomputable section

namespace Formalism.L2.Pj.CompFin

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteType_zero (R : Type) [CommRing R] (N : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _ (⟨MvPolynomial.C r, (MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_C _ r)⟩ : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (by simp))

theorem quasiCompact_str (R : Type) [CommRing R] (N : ℕ) : QuasiCompact (PSpace.str R N) := by
  haveI := finiteType_zero R N
  unfold PSpace.str
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem quasiCompact_alt (Xo : Moduli Dw l) : QuasiCompact Xo.s := by
  obtain ⟨N, i, -, hq, h⟩ := Xo.qproj
  haveI := hq
  haveI := quasiCompact_str (KA l) N
  rw [← h]
  infer_instance

theorem isNoetherian_XF (Xo : Moduli Dw l) (c : Coeff l) : IsNoetherian (Xo.XF c) := by
  obtain ⟨N, i, hi, hq, h⟩ := Xo.qproj
  haveI := hq
  haveI := hi
  haveI := finiteType_zero (KA l) N
  have hsurj : Function.Surjective
      (algebraMap (KA l) (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (KA l) 0)) := by
    rintro ⟨x, hx⟩
    have hx' := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hx
    refine ⟨AddMonoidAlgebra.coeff x 0, Subtype.ext ?_⟩
    rcases eq_or_ne x 0 with rfl | h0
    · simp
    · exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (hx'.totalDegree h0)).symm
  haveI : IsClosedImmersion
      (spMap (algebraMap (KA l) (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (KA l) 0))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  haveI : LocallyOfFiniteType Xo.s := by
    rw [← h]
    unfold PSpace.str
    infer_instance
  haveI := quasiCompact_alt Xo
  constructor

theorem finite_comp (Xo : Moduli Dw l) (c : Coeff l) : Finite (Comp Xo c) := by
  haveI := isNoetherian_XF Xo c
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype

end Formalism.L2.Pj.CompFin
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Open

variable (Xo : Moduli Dw l) (c : Coeff l)

def WtField : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S),
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y →
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y' →
      FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

def IntDiagUnit : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ),
    (letI := io.toAlgebra; FrBor t y.1 y'.1) → ∀ i, valV T.V ((t i : T.Frˣ) : T.Fr) = 1

def AlgPtLa : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e),
    T.FinRes ∧ ∃ x : Sp T.Fr ⟶ Xo.X, (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr)

def IntFrExt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → ∀ x : Sp T.Fr ⟶ Xo.X, (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) →
    ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r ∧ (∀ z, vV T'.V (i z) = (r : ℤ) * vV T.V z) ∧ T'.FinRes ∧
      ∃ y : IntFr Xo c T' (i.comp io), (letI := (i.comp io).toAlgebra; y.1.x = spMap i ≫ x)

end Open

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem valV_wchar_eq_one {T : CDVR} (e : Ix Dw → ℕ) (t : Ix Dw → T.Frˣ)
    (ht : ∀ i, valV T.V ((t i : T.Frˣ) : T.Fr) = 1) : valV T.V (wchar e t) = 1 := by
  simp [wchar, map_prod, map_pow, ht]

private theorem vV_mul_lemma {T : CDVR} {w x : T.Fr} (hu : valV T.V w = 1) (hx : x ≠ 0) :
    vV T.V (w * x) = vV T.V x := by
  unfold vV
  rw [map_mul, hu, one_mul]

theorem unitIndep_of (hW : WtField Xo c) (hU : IntDiagUnit Xo c) : UnitIndep Xo c := by
  intro a n f hf T io y y' t hb e
  letI := io.toAlgebra
  have hw := hW a n f hf T.Fr t y.1 y'.1 y.2.1 y'.2.1 hb
  have hu := valV_wchar_eq_one (ex Dw a n) t (hU T io y y' t hb)
  unfold nval evI
  rw [hw]
  generalize evR Xo c f y.1 = x at *
  have hne : wchar (ex Dw a n) t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact zero_ne_one hu
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (mul_ne_zero hne hx), if_neg hx, vV_mul_lemma hu hx]

theorem intFrNe_of (hA : AlgPtLa Xo c) (hE : IntFrExt Xo c) :
    IntFrNe Xo c (fun _ _ y => IntFr.IsAlg y) := by
  intro la
  obtain ⟨T, io, e, hO, hF, x, hx⟩ := hA la
  obtain ⟨T', i, r, hr, hv, hF', y, hy⟩ := hE T io hF x hx
  unfold OverLa IntFr.IsAlg at *
  refine ⟨T', i.comp io, r * e, ⟨Nat.mul_pos hr hO.1, fun a => ?_⟩, y, hF'⟩
  rw [RingHom.comp_apply, hv, hO.2 a]
  push_cast
  ring

end Proofs

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
section
noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  sec Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laU (U σ) a n)).comap (rdU (U σ))

theorem cusp_le_sec (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n ≤ sec Xo c a n := inf_le_left

theorem mem_cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    f ∈ cusp Xo c U a n ↔ f ∈ sec Xo c a n ∧ ∀ σ : c.F →+* ℂ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) := by
  simp only [cusp, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]

def mulC (f g : Rul Xo c) : Rul Xo c := f * g

theorem mulC_mem_sec (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : mulC Xo c f g ∈ sec Xo c (a + a') (n + n') := sec_mul Xo c a a' n n' hf hg

def CuspMul : Prop :=
  ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), Dom a n → Dom a' n' → f ∈ cusp Xo c U a n →
    g ∈ cusp Xo c U a' n' → mulC Xo c f g ∈ cusp Xo c U (a + a') (n + n')

set_option maxSynthPendingDepth 1 in
def CuspFD : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n)

end Formalism.L2.PjFree
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.HeckeFr
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def hkKer (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) :
    Type :=
  {C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y.x) Dw 𝔓 p i C}

def IsHkIsog {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : ℕ) (y y'' : Sp Ω ⟶ Xo.X)
    (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G)) : Prop :=
  y'' ≫ Xo.s = y ≫ Xo.s ∧ ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ (∀ x, fibPt _ x ≫ ψ = fibPt _ (ψp x)) ∧
    (∀ a x, ψp (x ≫ Xo.univ.t.act.act a) = ψp x ≫ Xo.univ.t.act.act a) ∧
    Function.Surjective ψp ∧ ψp.ker = C ∧
    (∀ (n : ℕ) (x x' : Over.mk y ⟶ Xo.univ.t.G) (u : Ωˣ), n.Coprime p →
      ReciprocityTheory.ChartRestriction.G.Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn u) →
      ReciprocityTheory.ChartRestriction.G.Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (ψp x) (ψp x') (unitOn (u ^ (p ^ 2)))) ∧
    ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a,
      ψp (toUnit _ ≫ Xo.univ.eta (p' • a)) = toUnit _ ≫ Xo.univ.eta a ∧
      ψp (toUnit _ ≫ Xo.univ.etaA (p' • a)) = toUnit _ ≫ Xo.univ.etaA a

def IsLieImageH {Ω : Type} [Field Ω] (p : ℕ) {y y'' : Sp Ω ⟶ Xo.X}
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (v v' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber Ω) ⟶ pullback Xo.univ.t.G.hom y,
    w ≫ pullback.fst _ _ = v ∧ w ≫ pullback.snd _ _ = spMap (algebraMap Ω (DualNumber Ω)) ∧
      v' = spMap (epsMul ((p : Ω)⁻¹)) ≫ w ≫ ψ ≫ pullback.fst _ _

def HkPt (p : ℕ) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (sTr : ∀ (y z : FrPt Xo c Ω), (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (y : FrPt Xo c Ω) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)) (z : FrPt Xo c Ω) : Prop :=
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)),
    IsHkIsog p y.x z.x C ψ ψp ∧ (∀ τ j, IsLieImageH p ψ (y.u τ j) (z.u τ j)) ∧ sTr y z ψ

def hkRelFr (𝔓 : Ideal (𝓞 E)) (p i : ℕ)
    (sTr : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y z : FrPt Xo c Ω),
      (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) 𝔓 p i Ω y)
    (z : FrPt Xo c Ω) : Prop :=
  HkPt p (sTr Ω) y C.1 z

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.PtFree
section
noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section One

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]

structure IsVal (la : HeightOneSpectrum (𝓞 K)) (v : R → EReal) : Prop where
  zero : v 0 = ⊤
  ne_bot : ∀ r, v r ≠ ⊥
  add : ∀ r s, min (v r) (v s) ≤ v (r + s)
  smul : ∀ (a : K) r, a ≠ 0 → v (a • r) = (((vLa la a : ℤ) : ℝ) : EReal) + v r
  mul : ∀ r s, v (r * s) = v r + v s

end One

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)

def algCls (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop := y.IsAlg

def valSet (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  Set.range (vAtV : PtV Xo c cls Unit (fun _ _ _ _ => True) la → Rul Xo c → EReal)

variable {Xo c cls}

theorem isVal_vAt {PY : Type} {lies : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) : IsVal la (vAtV y) := by
  obtain ⟨⟨g, hg⟩, T, io, e, hO, y0, hcls, eta, hl, heq⟩ := y
  unfold vAtV
  dsimp only
  unfold profI at heq
  have hg1 := congrArg Prod.fst heq
  dsimp only at hg1
  subst hg1
  have h0 : evI y0 (0 : Rul Xo c) = 0 := by
    have h := evI_add y0 (0 : Rul Xo c) 0
    simp only [add_zero] at h
    apply add_left_cancel (a := evI y0 0)
    simpa only [add_zero] using h.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show nval T.V e (evI y0 0) = ⊤
    rw [h0, nval_zero]
  · intro r
    show nval T.V e (evI y0 r) ≠ ⊥
    by_cases hr : evI y0 r = 0
    · rw [hr, nval_zero]
      simp
    · rw [nval_of_ne hr]
      exact EReal.coe_ne_bot _
  · intro r s
    show min (nval T.V e (evI y0 r)) (nval T.V e (evI y0 s)) ≤ nval T.V e (evI y0 (r + s))
    rw [evI_add]
    exact nval_add e _ _
  · intro a r ha
    show nval T.V e (evI y0 (a • r)) = (((vLa la a : ℤ) : ℝ) : EReal) + nval T.V e (evI y0 r)
    have hio : nval T.V e (io a) = (((vLa la a : ℤ) : ℝ) : EReal) := by
      rw [nval_of_ne ((map_ne_zero io).2 ha), hO.2 a]
      congr 1
      have he : (e : ℝ) ≠ 0 := by exact_mod_cast hO.1.ne'
      push_cast
      field_simp
    rw [evI_smul, nval_mul, hio]
  · intro r s
    show nval T.V e (evI y0 (r * s)) = nval T.V e (evI y0 r) + nval T.V e (evI y0 s)
    rw [evI_mul, nval_mul]

theorem isVal_valSet (la : HeightOneSpectrum (𝓞 c.F)) : ∀ v ∈ valSet Xo c cls la, IsVal la v := by
  rintro v ⟨y, rfl⟩
  exact isVal_vAt y

variable (Xo c cls)

variable {Xo c cls}

end Formalism.L2.PjFree
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ThProps
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ThValTot (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∃! v, ThValAt Xo c nab y x P v

def LastPos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ τ : E →+* ℂ, InPsi H τ → 0 < Dw.mult τ → 0 < a (τ, Dw.mult τ - 1)

def ThInCusp (nab : NabV Xo c)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a →
    ∀ f ∈ thGen Xo c nab a n, f ∈ cusp a n

def DF (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)

def ThNe0 (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 0 < n → Dw.p + Dw.q ≤ n → DF Dw a + 2 ≤ l.M →
    (∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) → ∃ f ∈ thGen Xo c nab a n, f ≠ 0


theorem existsUnique_thRule (nab : NabV Xo c) (h : ThValTot Xo c nab) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (x : Fin n → Dw.La) {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) :
    ∃! f : Rul Xo c, IsThRule Xo c nab x P f := by
  refine ⟨fun p y => (h p.R y a n x P hP).exists.choose,
    fun p y => (h p.R y a n x P hP).exists.choose_spec, ?_⟩
  intro g hg
  funext p y
  exact (h p.R y a n x P hP).unique (hg p y) (h p.R y a n x P hP).exists.choose_spec

end Formalism.L2.Pj
end
end

