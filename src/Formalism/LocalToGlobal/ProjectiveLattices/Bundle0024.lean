module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CompTie
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def OrdTie (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)) (la : HeightOneSpectrum (𝓞 c.F)),
    IsNormDiscrete v → IsOver (K := c.F) v la →
    ∃ y : PtV Xo c cls (PY la) (lies la) la,
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = (((ramIdx (K := c.F) v la : ℤ) : ℝ) : EReal) * vAtV y f

def OrdTieQ (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v → IsTrivOn c.F v →
    ∃ q : QPt Xo c, ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
      (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CompTieA
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem vAtV_mem_valSet {cls cls' : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop}
    (hc : ∀ T io y, cls T io y → cls' T io y) {PY : Type}
    {lies : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) :
    vAtV y ∈ valSet Xo c cls' la := by
  unfold vAtV valSet
  refine ⟨⟨((y.1).1, ()), ?_⟩, rfl⟩
  obtain ⟨T, io, e, hO, y1, hcl, eta, -, hy⟩ := y.2
  refine ⟨T, io, e, hO, y1, hc T io y1 hcl, (), trivial, ?_⟩
  rw [hy]
  rfl

theorem valC_add (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f g : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (f + g) Z = valC h a n f Z + valC h a n g Z := by
  simp only [valC, evC, evR]
  rw [evalAt_add, AddMonoidAlgebra.single_add]

theorem valC_zero (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Z : Comp Xo c) :
    valC h a n 0 Z = 0 := by
  simp only [valC, evC, evR]
  rw [evalAt_zero, AddMonoidAlgebra.single_zero]

theorem valC_smul_ct (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : c.F) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (t • f) Z = algebraMap c.F (AC Z) t * valC h a n f Z := by
  simp only [valC, evC, evR]
  rw [evalAt_smul, ← Algebra.smul_def, ← Algebra.smul_def, AddMonoidAlgebra.smul_single]

theorem evC_ne_zero_of_valC {h : GenFrEx Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} {Z : Comp Xo c}
    (hf : valC h a n f Z ≠ 0) : evC h Z f ≠ 0 := by
  intro h0
  apply hf
  unfold valC
  rw [h0, AddMonoidAlgebra.single_zero]

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def offZero {Comp : Type} (X : Comp → Data E r) : Submodule ℂ (FDSec X) where
  carrier := {P | ∀ k x, x ∉ (X k).dom → P k x = 0}
  zero_mem' _ _ _ := rfl
  add_mem' hP hQ k x hx := by simp [hP k x hx, hQ k x hx]
  smul_mem' a P hP k x hx := by simp [hP k x hx]

def holSub0 {Comp : Type} (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) : Submodule ℂ (FDSec X) :=
  holSub X la ⊓ offZero X

variable {Xo c} in
theorem rdU_mem_offZero {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (f : Rul Xo c) : rdU V f ∈ offZero V.X :=
  fun _ _ hx => dif_neg hx


end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Core (D : D7) : Type 1 where
  Q : Par D
  U : ∀ j (σ : Q.c.F →+* ℂ), Unf (Q.Xo j) Q.c σ D.R.r
  V : ℕ → (Q.c.F →+* ℂ) → HSp D
  dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r
  mu : ∀ j σ, GA D (V j σ) → ℂ
  Kf : ∀ j σ, Subgroup (GA D (V j σ))
  pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)

variable {D : D7}

def latHat (V : HSp D) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ a : Af D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) ∧
    ∃ x ∈ V.L0, z = fun i => a ⊗ₜ V.frame.repr x i}

def IsLevelK (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y

def xiR (D : D7) : ℝ := ‖D.host.φ₀ D.host.xi0‖

namespace Core

variable (T : Core D)

def σ₀ : T.Q.c.F →+* ℂ := T.Q.c.F.val.toRingHom

theorem good_σ₀ : GoodEmb T.Q.c T.σ₀ := rfl

abbrev R (j : ℕ) : Type := Rul (T.Q.Xo j) T.Q.c

abbrev cuspA (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule T.Q.c.F (T.R j) :=
  cusp (T.Q.Xo j) T.Q.c (T.U j) a n

abbrev X₀ (j : ℕ) : (T.U j T.σ₀).Comp → Data D.host.E D.R.r := (T.U j T.σ₀).X

def frI (_T : Core D) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := 1

abbrev PtM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

def nrmM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) : ℝ := nrmOf la (y.1 f)

theorem nrmM_le_one_iff (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) :
    T.nrmM j la y f ≤ 1 ↔ 0 ≤ y.1 f := by
  unfold nrmM nrmOf
  have hy := y.2
  unfold valSet at hy
  obtain ⟨x, hx⟩ := hy
  unfold vAtV at hx
  obtain ⟨T1, io, e, -, y', -, eta, -, hxe⟩ := x.2
  rw [hxe] at hx
  unfold profI at hx
  have key : y.1 f = nval T1.V e (evI y' f) := by rw [← hx]
  unfold nval at key
  have hN : (1 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
    have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    have h1 : Ideal.absNorm la.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact la.isPrime.ne_top
    exact_mod_cast (by omega : 1 < Ideal.absNorm la.asIdeal)
  rw [key]
  by_cases hz : evI y' f = 0
  · simp [hz]
  · simp only [hz, if_false, EReal.coe_ne_top, EReal.toReal_coe, EReal.coe_nonneg]
    constructor
    · intro h
      by_contra hneg
      exact absurd h (not_le.mpr (Real.one_lt_rpow hN (neg_pos.mpr (not_le.mp hneg))))
    · intro h
      exact Real.rpow_le_one_of_one_le_of_nonpos hN.le (neg_nonpos.mpr h)

def phiAd (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) • adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f)

end Core

structure LawsM (T : Core D) : Prop where

  pins : T.Q.Pins

  half : (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal) ∧
    T.Q.l.Mb = ∏ k, (T.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

  evalWD : ∀ j, InR D j → EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)

  unf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ)

  unTest : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k x,
    FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) ((T.U j σ).un k x)
  chiTriv : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
    ((T.U j σ).X k).χ (laU (T.U j σ) a n k) γ = 1

  dictU : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (T.V j σ) (T.dict j σ) (T.Kf j σ) th hr

  spaceW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → T.V j σ = D.sp.W j
  levelK : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsLevelK (T.V j σ) (D.host.g 0 * D.host.g 1) (T.Kf j σ)

  xiAbs : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((T.U j σ).X k).ξ0‖ = xiR D
  muUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuUnit (T.V j σ) (T.dict j σ) (T.mu j σ)
  muCont : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → Continuous (T.mu j σ)
  finVol : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → FinVol (T.V j σ)

  cuspFD : ∀ j, InR D j → CuspFD (T.Q.Xo j) T.Q.c (T.U j)

  supDef : ∀ j, InR D j → SupDef (T.Q.Xo j) T.Q.c (T.U j)

  cuspidalL2Subspace : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ)
  l2Def : ∀ j (hj : InR D j) σ (hσ : GoodEmb T.Q.c σ),
    L2DefiniteCuspForms (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) (cuspidalL2Subspace j hj σ hσ)

  unitIndep : ∀ j, InR D j → UnitIndep (T.Q.Xo j) T.Q.c
  ptNe : ∀ j, InR D j → IntFrNe (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)

structure LawsCore (T : Core D) : Prop extends LawsM T where

  cuspMul : ∀ j, InR D j → CuspMul (T.Q.Xo j) T.Q.c (T.U j)

  latZ : ∀ j, InR D j → FJ.LatZ (T.X₀ j) (WeightFamilies.rho D j)
  cuNe : ∀ j, InR D j → FJ.CuNeF (T.X₀ j) (WeightFamilies.rho D j)
  expo : ∀ j, InR D j → FJ.ExpoMatch (T.X₀ j) T.frI (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
section
noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

end Sections

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def Unf.ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

def Unf.toPj (U : Unf Xo c σ r) : Formalism.L2.Pj.Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

theorem rdU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (f : Formalism.L2.Pj.Rul Xo c) : rdU (Unf.ofPj U) f = Formalism.L2.Pj.rdU U f := rfl

theorem laU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) :
    laU (Unf.ofPj U) a n k = Formalism.L2.Pj.laU U a n k := rfl

theorem isUnf_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : IsUnf (Unf.ofPj U) ↔ Formalism.L2.Pj.IsUnf U := by rfl

theorem goodEmb_iff (σ : c.F →+* ℂ) : GoodEmb c σ ↔ Formalism.L2.Pj.GoodEmb c σ := by rfl

variable (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)

theorem cusp_ofPj (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (fun σ => Unf.ofPj (U σ)) a n = Formalism.L2.Pj.cusp Xo c U a n := rfl

theorem cuspMul_ofPj : CuspMul Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspMul Xo c U := by rfl

theorem cuspFD_ofPj : CuspFD Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspFD Xo c U := by rfl

theorem supDef_ofPj : SupDef Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.SupDef Xo c U := by rfl

theorem regP_ofPj : regular₂ Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.regular₂ Xo c U := by rfl

end Unif

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l) (cls : ∀ (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr), Formalism.L2.Pj.IntFr Xo c T ι → Prop)

end Points

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {r : ℕ}

end Frames

end Formalism.L2.PjFree
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LocFrGen
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}


set_option maxHeartbeats 400000 in
theorem locFrGen_of {L : Type} [CommRing L] (x : Sp L ⟶ Xo.X) {t' : SAB H (Sp L)} (m1 : SABMap t' Xo.univ.t x)
    (σ' : LB.Sec t'.PP.L) (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : L, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w, hwG, -, -⟩ := m1.lin
  have hw : PGen w := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).mp hwG
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s0, hs0⟩ := thf_secUp hw hL hL' σ'
  have P' := m1.cart.1
  obtain ⟨h, hF, hS⟩ : ∃ h : Gx x ⟶ t'.G.left, h ≫ m1.cm.F = (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left ∧ h ≫ t'.G.hom = (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨P'.lift _ _ ((Over.w (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)).symm),
      P'.lift_fst _ _ _, P'.lift_snd _ _ _⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : t'.G.left ⟶ Gx x, k ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom ∧ k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m1.cm.F :=
    ⟨(CartesianMonoidalCategory.lift
        (Over.homMk t'.G.hom P'.w.symm : Over.mk (m1.cm.F ≫ Xo.univ.t.G.hom) ⟶ Over.mk x)
        (Over.homMk m1.cm.F rfl : Over.mk (m1.cm.F ≫ Xo.univ.t.G.hom) ⟶ Xo.univ.t.G)).left,
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst _ _),
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd _ _)⟩
  have gext : ∀ u v : Gx x ⟶ Gx x, u ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = v ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left → u ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = v ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left → u = v := by
    intro u v e1 e2
    have e3 : (Over.homMk u rfl : Over.mk (u ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G) =
        Over.homMk (U := Over.mk (u ≫ (Over.mk x ⊗ Xo.univ.t.G).hom)) (V := Over.mk x ⊗ Xo.univ.t.G) v (by
          show v ≫ _ = u ≫ _
          rw [← Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G), ← Category.assoc,
            ← Category.assoc, e1]) := by
      apply CartesianMonoidalCategory.hom_ext
      · first | exact Over.OverMorphism.ext e1 | exact Over.Hom.ext e1 | (ext; exact e1)
      · first | exact Over.OverMorphism.ext e2 | exact Over.Hom.ext e2 | (ext; exact e2)
    exact congrArg Over.Hom.left e3
  have hhk : h ≫ k = 𝟙 _ := gext _ _ (by rw [Category.assoc, hk1, hS, Category.id_comp])
    (by rw [Category.assoc, hk2, hF, Category.id_comp])
  have hkh : k ≫ h = 𝟙 _ := P'.hom_ext (by rw [Category.assoc, hF, hk2, Category.id_comp])
    (by rw [Category.assoc, hS, hk1, Category.id_comp])
  have hle : ∀ j, m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ k ⁻¹ᵁ (PPx x).U (fun _ => j) := fun j z hz =>
    Set.mem_iInter.mpr fun _ => Set.mem_iInter.mp
      (chart_le_pullback_open Xo.univ.t.PP.L k hk2 (fun _ => j) (Set.mem_iInter.mpr fun _ => hz)) PUnit.unit
  have hpre : ∀ (z : t'.G.left) j, z ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) →
      z ∈ m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z j hz => Set.mem_iInter.mp hz PUnit.unit
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF s0, fun s'' => ?_⟩
  obtain ⟨σ'', hσ''⟩ := sec_down hw hL hL'
    (fun j => (k.appLE ((PPx x).U (fun _ => j)) (m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j) (hle j)).hom
      (s''.f (fun _ => j))) (by
      intro y j j' hj hj'
      try beta_reduce
      have h1 : k y ∈ (PPx x).U (fun _ => j) := hle j hj
      have h2 : k y ∈ (PPx x).U (fun _ => j') := hle j' hj'
      have hg : gm (𝟙 _ ≫ k) y ((PPx x).U (fun _ => j) ⊓ (PPx x).U (fun _ => j'))
          ((PPx x).g (fun _ => j) (fun _ => j')) =
          gm m1.cm.F y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
        (gm_linComb Xo.univ.t.PP.L (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => 1) (𝟙 _ ≫ k) y
          (fun _ => j) (fun _ => j') h1 h2).trans (by rw [Fin.prod_univ_one, zpow_one, Category.id_comp, hk2])
      rw [gs_appLE k _ _ (hle j) (𝟙 _) y hj, gs_appLE k _ _ (hle j') (𝟙 _) y hj',
        gs_compat s'' (𝟙 _ ≫ k) y h1 h2, hg])
  obtain ⟨a, ha, hau⟩ := hgen σ''
  refine ⟨a, fun J => ?_, fun b hb => hau b fun i => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, J = fun _ => j := ⟨J 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
    apply fn_ext
    intro y hy
    have hyh : h y ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) :=
      chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j) hy
    obtain ⟨i, hi⟩ : ∃ i, h y ∈ t'.PP.L.U i := TopologicalSpace.Opens.mem_iSup.mp (by
      rw [hL'.cover]
      first | trivial | exact Set.mem_univ _ | simp)
    have e1 := gs_appLE k _ _ (hle j) h y (hpre _ _ hyh) (s''.f (fun _ => j))
    rw [hhk] at e1
    have e2 := hσ'' _ h y j i (hpre _ _ hyh) hi
    have e3 := hs0 _ h y (fun _ => j) i hyh hi
    have e4 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s0).f (fun _ => j)) =
        gs (𝟙 _ ≫ h) y _ (s0.f (fun _ => j)) := gs_appLE h _ _ _ (𝟙 _) y hy _
    rw [Category.id_comp] at e4
    have e5 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) (scal x a (fun _ => j)) = cst (𝟙 _ ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y a :=
      gs_constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _) y hy a
    rw [gs_mul (𝟙 _) y _ hy, e4, e3, e5, ← e1, e2, ha i, gs_mul h y _ hi, gs_constFn t'.G.hom _ h y hi a,
      hS, Category.id_comp]
    ring
  · apply fn_ext
    intro y' hy'
    obtain ⟨j, hj⟩ : ∃ j, m1.cm.F y' ∈ Xo.univ.t.PP.L.U j := TopologicalSpace.Opens.mem_iSup.mp (by
      rw [hL.cover]
      first | trivial | exact Set.mem_univ _ | simp)
    have hkm : k y' ∈ (PPx x).U (fun _ => j) := hle j hj
    have hmem : y' ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) := Set.mem_iInter.mpr fun _ => hj
    have f1 := hσ'' _ (𝟙 _) y' j i hj hy'
    have f2 := gs_appLE k _ _ (hle j) (𝟙 _) y' hj (s''.f (fun _ => j))
    have f3 : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) (scal x b (fun _ => j)) = cst ((𝟙 _ ≫ k) ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y' b :=
      gs_constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _ ≫ k) y' hkm b
    have f4 : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s0).f (fun _ => j)) =
        gs ((𝟙 _ ≫ k) ≫ h) y' _ (s0.f (fun _ => j)) := gs_appLE h _ _ _ (𝟙 _ ≫ k) y' hkm _
    rw [Category.assoc, hkh, Category.comp_id] at f4
    have f5 := hs0 _ (𝟙 _) y' (fun _ => j) i hmem hy'
    have f2b : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) (s''.f (fun _ => j)) =
        cst ((𝟙 _ ≫ k) ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y' b *
          gs (𝟙 _) y' ((Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j)) (s0.f (fun _ => j)) := by
      rw [hb (fun _ => j), gs_mul (𝟙 _ ≫ k) y' _ hkm, f3, f4]
    rw [f5] at f2b
    have f6 := (f1.symm.trans f2).trans f2b
    rw [Category.id_comp, hk1, mul_left_comm] at f6
    rw [gs_mul (𝟙 _) y' _ hy', gs_constFn t'.G.hom _ (𝟙 _) y' hy' b, Category.id_comp]
    exact (Units.mul_right_inj _).mp f6

end Formalism.L2.Pj
end
end

