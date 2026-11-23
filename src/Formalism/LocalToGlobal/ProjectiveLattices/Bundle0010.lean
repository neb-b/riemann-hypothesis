module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AllTest
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def AllTest : Prop :=
  ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def CubIso {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec Xo.univ.t.G) (fun _ => 1)) Xo.univ.t.PP.rig
      (ν.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε) Xo.univ.t.cub.t
      (ν.cm.thetaPull Xo.univ.t.PP.L Xo.univ.t.cub.t)

def IsLevMove (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ρ ≫ Xo.s = Xo.s ∧
    (∀ a, (Xo.univ.eta (gM a)).left ≫ ν.φ = ρ ≫ (Xo.univ.eta a).left) ∧
    (∀ a, (Xo.univ.etaA (gA a)).left ≫ ν.φ = ρ ≫ (Xo.univ.etaA a).left)

def FrMove {S : Type} [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (y y' : FrPt Xo c S) : Prop :=
  y'.x = y.x ≫ ρ ∧
    (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) ∧
    ∃ (pm : Gx y.x ⟶ Gx y'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)),
      pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left ∧
      pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ ∧
      CubIso ν w ∧
      ∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx y.x).Opens),
        W = (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
          ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) →
        ∀ (h₀ : W ≤ (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
              ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)))
          (h₁ : W ≤ pm ⁻¹ᵁ (PPx y'.x).U (fun _ => i)) (h₂ : W ≤ (PPx y.x).U (fun _ => j)),
        (pm.appLE ((PPx y'.x).U (fun _ => i)) W h₁).hom (y'.s.f (fun _ => i)) =
          ((snd (Over.mk y.x) Xo.univ.t.G).left.appLE
              ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) W h₀).hom
              (Units.val (w.s ((fun _ => i), j))) *
            ((Gx y.x).presheaf.map (homOfLE h₂).op).hom (y.s.f (fun _ => j))

def levR (g : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : Prop :=
  ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), IsIso ρ ∧ IsLevMove ρ ν g.1 g.2 ∧ FrMove ρ ν y y'

def levActR {G : Type} (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (gm : G) {S : Type} [CommRing S]
    [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  levR (Xo := Xo) (c := c) (lev gm) y y'

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev Lt1 (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

abbrev ptO {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Over Xo.X := Over.mk x

abbrev NabV : Type 1 :=
  ∀ {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ),
    LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)) → (Lt1 Dw →₀ ℕ) → S

section Vt

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def IsVtOver (N : ℕ) {T : Over X} (ok : (T ⟶ A) → Prop) (s : LB.Sec (LPow A L.L 1 T)) (t : T ⟶ A)
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  ∃ (t' : T ⟶ A)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]))
    (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
    t' ^ N = t ∧ ok t' ∧ α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) t' U ∧ IsActOf A L.L ((N : ℤ) ^ 2) U s₁ F

end Vt

abbrev LtN (Dw : Datum H) (n : ℕ) : Type := Letter (E →+* ℂ) Dw.mult n

def colOf {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) : Lt1 Dw →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩

def levPt {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (x : Dw.La) : ptO Xo x0 ⟶ Xo.univ.t.G :=
  toUnit _ ≫ Xo.univ.eta x

def KilledBy (I : Ideal (𝓞 E)) {T : Over Xo.X} (t' : T ⟶ Xo.univ.t.G) : Prop :=
  ∀ a ∈ I, t' ≫ Xo.univ.t.act.act a = 1

def thExpr (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (P : MvPolynomial (LtN Dw n) c.F)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x))) : S :=
  algebraMap c.F S (((l.M : c.F) ^ P.totalDegree)⁻¹) *
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((l.M : ℤ) ^ 2) (F b) (colOf m b)

def ThValAt (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y'.x))),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧
    (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s (levPt Xo y'.x (x b)) (F b)) ∧
    φ v = thExpr Xo c nab y' P F

def IsThRule (nab : NabV Xo c) {n : ℕ} (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F)
    (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ThValAt Xo c nab y x P (f p y)

def InPsi (H : Host E) (τ : E →+* ℂ) : Prop := τ (H.rt : E) = H.rt0

def harmA (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (MvPolynomial (LtN Dw n) c.F) :=
  HaO Dw.mult n c.F (integralClosure ℤ c.F).toSubring ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)

def thGen (nab : NabV Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n ∧
    IsThRule Xo c nab x P f}

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Bundles

variable {X Y : Scheme.{0}}

def IsoMaps {L M : LB X} (w : LB.Iso L M) (s : LB.Sec L) (s' : LB.Sec M) : Prop :=
  ∀ (i : M.ι) (k : L.ι),
    (X.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ L.U k ≤ M.U i)).op).hom (s'.f i) =
      (show Γ(X, M.U i ⊓ L.U k) from (w.s (i, k) : Γ(X, (LB.div M L).U (i, k)))) *
        (X.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ L.U k ≤ L.U k)).op).hom (s.f k)

def PullSec {L : LB X} (f : Y ⟶ X) (s : LB.Sec L) (s' : LB.Sec (L.pull f)) : Prop :=
  ∀ j (h : (L.pull f).U j ≤ f ⁻¹ᵁ L.U (j PUnit.unit)), s'.f j = (f.appLE _ _ h).hom (s.f (j PUnit.unit))

end Bundles

section Sab

variable {S S' : Scheme.{0}}

def RigIso {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) : Prop :=
  w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
    (m.cm.rigPull t.PP.L t.PP.rig)

end Sab

section Integral

variable (Xo : Moduli Dw l) (c : Coeff l)

def IsEigV {V Fr : Type} [CommRing V] [Field Fr] [Algebra V Fr] (io : c.F →+* Fr) (G : SAB H (Sp V))
    (τ : E →+* ℂ) (v : epsOver V V ⟶ G.G) : Prop :=
  ∀ (a : 𝓞 E) (z : V), algebraMap V Fr z = io (embK c τ a) →
    (v ≫ G.act.act a).left = spMap (epsMul z) ≫ v.left

variable {Xo c}

def Integral (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) : Prop :=
  letI := io.toAlgebra
  ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    (∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G),
      (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧
      (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w →
        ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧
      ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = y.u τ i ∧
        u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) ∧
    ∃ θ : LB.Sec G.PP.L,
      (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
        σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧
      ∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ))
        (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)),
        RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧
        ∀ g : t'.G.left ⟶ Gx y.x, g ≫ (CartesianMonoidalCategory.snd (Over.mk y.x) Xo.univ.t.G).left = m1.φ →
          g ≫ (CartesianMonoidalCategory.fst (Over.mk y.x) Xo.univ.t.G).left = t'.G.hom →
          ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)),
            s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))

variable (Xo c)

def IntFr (T : CDVR) (io : c.F →+* T.Fr) : Type :=
  letI := io.toAlgebra
  {y : FrPt Xo c T.Fr // FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y ∧
    Integral T io y}

variable {Xo c}

def IntFr.IsAlg {T : CDVR} {io : c.F →+* T.Fr} (_y : IntFr Xo c T io) : Prop := T.FinRes

def evI {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (f : Rul Xo c) : T.Fr :=
  letI := io.toAlgebra
  evR Xo c f y.1

theorem evI_add {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (f g : Rul Xo c) :
    evI y (f + g) = evI y f + evI y g := by
  let := io.toAlgebra
  exact evalAt_add _ _ f g y.1

theorem evI_smul {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (a : c.F) (f : Rul Xo c) :
    evI y (a • f) = io a * evI y f := by
  let := io.toAlgebra
  exact evalAt_smul _ _ a f y.1

theorem evI_mul {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (f g : Rul Xo c) :
    evI y (f * g) = evI y f * evI y g := by
  let := io.toAlgebra
  exact evalAt_mul _ _ f g y.1

theorem isEval_evI {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) :
    IsEval (W := Unit) (Cusp := fun _ => Rul Xo c) (fun _ _ => ()) (fun _ _ f g => f * g) io
      (fun _ f => evI y f) :=
  ⟨fun _ f g => evI_add y f g, fun _ a f => evI_smul y a f, fun _ _ f g => evI_mul y f g⟩

section Points

variable (Xo c)
variable (cls : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) (PY : Type)
  (lies : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → PY → Prop)

def profI {T : CDVR} {io : c.F →+* T.Fr} (e : ℕ) (y : IntFr Xo c T io) (eta : PY) : (Rul Xo c → EReal) × PY :=
  (fun f => nval T.V e (evI y f), eta)

def PtV (la : HeightOneSpectrum (𝓞 c.F)) : Type :=
  {q : (Rul Xo c → EReal) × PY //
    ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (y : IntFr Xo c T io) (_ : cls T io y)
      (eta : PY) (_ : lies T io y eta), q = profI Xo c PY e y eta}

variable {Xo c cls PY lies}

def vAtV {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) (f : Rul Xo c) : EReal := y.1.1 f

def imgV {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) : PY := y.1.2

def PtV.mk (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    (y : IntFr Xo c T io) (hy : cls T io y) (eta : PY) (heta : lies T io y eta) : PtV Xo c cls PY lies la :=
  ⟨profI Xo c PY e y eta, T, io, e, ho, y, hy, eta, heta, rfl⟩

variable {la : HeightOneSpectrum (𝓞 c.F)}

theorem vAtV_zero (y : PtV Xo c cls PY lies la) : vAtV y 0 = ⊤ := by
  rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
  show nval T.V e (evI y 0) = ⊤
  rw [(isEval_evI y).zero (), nval_zero]

theorem vAtV_ne_bot (y : PtV Xo c cls PY lies la) (f : Rul Xo c) : vAtV y f ≠ ⊥ := by
  rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
  exact nval_ne_bot e _

theorem vAtV_add (y : PtV Xo c cls PY lies la) (f g : Rul Xo c) :
    min (vAtV y f) (vAtV y g) ≤ vAtV y (f + g) := by
  rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
  show min (nval T.V e (evI y f)) (nval T.V e (evI y g)) ≤ nval T.V e (evI y (f + g))
  rw [evI_add]; exact nval_add e _ _

theorem vAtV_smul (y : PtV Xo c cls PY lies la) (a : c.F) (f : Rul Xo c) (ha : a ≠ 0) :
    vAtV y (a • f) = (((vLa la a : ℤ) : ℝ) : EReal) + vAtV y f := by
  rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
  show nval T.V e (evI y (a • f)) = _ + nval T.V e (evI y f)
  rw [evI_smul]; exact nval_smul ho ha _

theorem vAtV_mul (y : PtV Xo c cls PY lies la) (f g : Rul Xo c) :
    vAtV y (f * g) = vAtV y f + vAtV y g := by
  rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
  show nval T.V e (evI y (f * g)) = nval T.V e (evI y f) + nval T.V e (evI y g)
  rw [evI_mul]; exact nval_mul e _ _

def PtV.widen {cls' : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop}
    (h : ∀ T io y, cls T io y → cls' T io y) (y : PtV Xo c cls PY lies la) : PtV Xo c cls' PY lies la :=
  ⟨y.1, by
    obtain ⟨T, io, e, ho, z, hz, eta, heta, hq⟩ := y.2
    exact ⟨T, io, e, ho, z, h T io z hz, eta, heta, hq⟩⟩

end Points

section Open

variable (Xo c)

def UnitIndep : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ),
      (letI := io.toAlgebra; FrBor t y.1 y'.1) → ∀ e : ℕ, nval T.V e (evI y f) = nval T.V e (evI y' f)

def IntFrNe (cls : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e)
    (y : IntFr Xo c T io), cls T io y

end Open

end Integral

end Formalism.L2.Pj
end
end

