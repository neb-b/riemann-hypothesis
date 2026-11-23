module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExistsFieldOfFf
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U)
    (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

theorem key_fwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i) :
    ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i := by
  rw [sec_eq_iff] at h
  rw [scal_eq_iff]
  intro J yy hy
  have hp : bcV ψ x yy ∈ (tB ψ x).PP.L.U (fun _ _ => J 0) := (cpV' ψ x).le J hy
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcV ψ x) yy hp (h _ _ hp)
  have A1 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0))
        ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f (fun _ _ => J 0)) =
      gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U (fun _ => J 0)) (s''.f (fun _ => J 0)) :=
    (gs_secCP (cpU' ψ x) s'' (bcV ψ x) yy _ hp).trans (by rw [bcV_bcU]; rfl)
  have hp2 : (bcV ψ x ≫ pullback.fst _ _) yy ∈
      (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).U (fun _ => J 0) := (cpσ ψ x).le _ hp
  have A2 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0)) ((σB ψ x s0).f (fun _ _ => J 0)) =
      gs (bcPm ψ x) yy ((PPx x).U (fun _ => J 0)) (s0.f (fun _ => J 0)) :=
    (gs_secCP (cpσ ψ x) (θA x s0) (bcV ψ x) yy _ hp).trans
      ((gs_secCP (cpθ x) s0 _ yy _ hp2).trans (by rw [Category.assoc, bcV_gxU]; rfl))
  have A3 : bcV ψ x ≫ (tB ψ x).G.hom = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := bcV_snd ψ x
  rw [A1, A2, A3] at h1
  have hJ : (fun _ : Fin 1 => J 0) = J := funext fun k => by rw [Subsingleton.elim k 0]
  rw [hJ] at h1
  have e4 : gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U J) ((secCP (cpS ψ x) s0).f J) =
      gs (bcPm ψ x) yy ((PPx x).U J) (s0.f J) :=
    (gs_secCP (cpS ψ x) s0 (𝟙 _) yy J hy).trans (by rw [Category.id_comp]; rfl)
  exact h1.trans (congrArg _ e4.symm)

theorem key_bwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i) :
    ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i := by
  rw [scal_eq_iff] at h
  rw [sec_eq_iff]
  intro i q hq
  have hq' : bcU ψ x q ∈ (PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit) := (cpU' ψ x).le i hq
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcU ψ x) q hq' (h _ _ hq')
  rw [bcU_fst] at h1
  have B0 : gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i) =
      gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        (s''.f (fun _ => i PUnit.unit PUnit.unit)) :=
    (gs_secCP (cpU' ψ x) s'' (𝟙 _) q i hq).trans (by rw [Category.id_comp]; rfl)
  have B1 : gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        ((secCP (cpS ψ x) s0).f (fun _ => i PUnit.unit PUnit.unit)) =
      gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((σB ψ x s0).f i) := by
    refine (gs_secCP (cpS ψ x) s0 (bcU ψ x) q _ hq').trans ?_
    rw [bcU_bcPm]
    exact ((gs_secCP (cpσ ψ x) (θA x s0) (𝟙 _) q i hq).trans
      ((gs_secCP (cpθ x) s0 _ q _ ((cpσ ψ x).le i hq)).trans (by rfl))).symm
  exact B0.trans (h1.trans (congrArg _ B1))

theorem genBC_frame (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    {K : Type} [Field K] (ρ : S →+* K) (s0 : LB.Sec (PPx x))
    (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i) (s'' : LB.Sec (PPx (spMap ρ ≫ x))) :
    ∃! a : K, ∀ i, s''.f i = scal (spMap ρ ≫ x) a i * (secCP (cpS ρ x) s0).f i := by
  obtain ⟨a, ha, hu⟩ := gen_baseChange hS hT Xo.univ (mA x) (θA x s0) (hθ_of x s0 hgen) ρ (mB ρ x)
    (w := idIso ((tA x).PP.L.pull (mB ρ x).φ)) (σB ρ x s0) (hσ_of ρ x s0) (secCP (cpU' ρ x) s'')
  exact ⟨a, key_fwd ρ x s0 s'' a ha, fun a' ha' => hu a' (key_bwd ρ x s0 s'' a' ha')⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem tvOf_tv {x : Sp S ⟶ Xo.X} (n : TanM x Xo.univ.t.G) :
    tvOf (isTanAtG_of (t := Xo.univ.t) (x0 := x) (tv n) (tv_mem n)) = n := by
  apply tanM_ext
  first
    | rfl
    | exact Over.OverMorphism.ext rfl
    | (ext; rfl)
    | (ext1; simp [tvOf, tv, mkT])
    | simp [tvOf, tv, mkT]

theorem eig_coords (y : FrPt Xo c S) (τ : E →+* ℂ) (n : TanM y.x Xo.univ.t.G)
    (hn : IsEigV (actR (x0 := y.x) (S := S) Xo.univ.t.act) (embK c τ) n) :
    ∃! a : Fin (Dw.mult τ) → S, n = ∑ i, a i • tvOf (y.tan τ i) := by
  have hw := isTanAtG_of (t := Xo.univ.t) (x0 := y.x) (tv n) (tv_mem n)
  have hE := (eigAt_iff c hw τ).2 (by rw [tvOf_tv]; exact hn)
  obtain ⟨a, ha, huniq⟩ := y.basis τ _ hw hE
  refine ⟨a, ?_, fun a' h' => huniq a' ((combAt_iff (y.u τ) (y.tan τ) a' hw).2 ?_)⟩
  · have h1 := (combAt_iff (y.u τ) (y.tan τ) a hw).1 ha
    rw [tvOf_tv] at h1
    exact h1
  · rw [tvOf_tv]
    exact h'

theorem eig_comb {x : Sp S ⟶ Xo.X} (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x Xo.univ.t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (v i)) (a : Fin m → S) :
    IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans Finset.smul_sum.symm
  rw [map_smul, hv i b]
  exact smul_comm _ _ _

def fullB (y : FrPt Xo c S) : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → TanM y.x Xo.univ.t.G :=
  fun k => tvOf (y.tan k.1 k.2)

theorem fullB_eig (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    IsEigV (actR (x0 := y.x) (S := S) Xo.univ.t.act) (embK c τ) (fullB y ⟨τ, i⟩) :=
  (eigAt_iff c (y.tan τ i) τ).1 (y.eig τ i)

theorem fullB_basis (y : FrPt Xo c S) (m : TanM y.x Xo.univ.t.G) :
    ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, m = ∑ k, a k • fullB y k := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := y.x) (S := S) Xo.univ.t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End S (TanM y.x Xo.univ.t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => eig_coords y τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), a k.1 k.2 • fullB y k
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b k • fullB y k := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • fullB y ⟨τ, i⟩)
      (fun τ => eig_comb τ _ (fun i => fullB_eig y τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NuChain
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V]

def iotaK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V)) :
    tK.G.left ⟶ pullback t.G.hom (Out.jK V) :=
  pullback.lift m.φ tK.G.hom m.cart.1.w

def secU {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t) {k : ℕ} (s : P.U.SecK k) :
    LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => pullback.fst t.G.hom (Out.jK V)) (fun _ => (k : ℤ))) :=
  P.bundle ▸ s

def SecTieGK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (P : PELUnif (IsLocalRing.maximalIdeal V) t) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) (s : P.U.SecK k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval (secU P s) (r ≫ iotaK m) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

def NuK {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t)
    (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)) {tK : SAB H (Sp (FractionRing V))}
    (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) : Prop :=
  ∃ (s : P.U.SecK k) (Ex : Fam P.D.toPre (FractionRing V) k),
    SecTieGK m w P k F s ∧ P.U.Expands k s Ex ∧ NuGe P.D Q (FractionRing V) vK k Ex 0

end Defs

def NuDataSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t),
    ∃ (ϖ : V) (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)),
      Irreducible ϖ ∧ QForm.IsQ P.D.toPre ϖ Q ∧ ValOver ϖ (FractionRing V) vK

def ThetaNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))))
      (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ → NuK P Q vK m w 1 θK

def MulNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (N : ℕ), 1 ≤ N → ∀ (s : LB.Sec (LPow tK.G tK.PP.L 1 (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (mulA tK.G N).left] ![(N : ℤ) ^ 2, -1]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N).left] ![(N : ℤ) ^ 2, -1]))
      (s₁ : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm s) → α₀.IsGen → IsNormMul tK.G tK.PP.L tK.PP.rig N α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (mulT tK.G (𝟙_ (Over (Sp (FractionRing V)))) N) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ →
      NuK P Q vK m w (N ^ 2) (zCast tK.G (natCast_sq N) s₁)

def EndNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (π : 𝓞 E) (n k : ℕ), 0 < k → ∀ (F₁ : LB.Sec (LPow tK.G tK.PP.L ((n : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (h₁ : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w (n ^ 2) (zCast tK.G (natCast_sq n) F₁) → α₀.IsGen →
      IsNormEnd tK.G tK.PP (tK.act.act π) (k : ℤ) ((n : ℤ) ^ 2) α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (endT tK.G (𝟙_ (Over (Sp (FractionRing V)))) (tK.act.act π)) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π)
        (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ →
      NuK P Q vK m w k h₁

def FinNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (a : ℤ) (k : ℕ) (ha : a = k), 0 < k → ∀ (h hh : LB.Sec (LPow tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))))
      (b : (𝟙_ (Over (Sp (FractionRing V)))) ⟶ tK.G) (U : ThetaGrp tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))),
      NuK P Q vK m w k (zCast tK.G ha h) → b ^ k = 1 → SymLift tK.G tK.PP.L a k b U → IsActOf tK.G tK.PP.L a U h hh →
      NuK P Q vK m w k (zCast tK.G ha hh)

def NuRegSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (k : ℕ), 0 < k → ∀ F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))), NuK P Q vK m w k F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))), SecTieK m w k F σ

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RdIndepOf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem rdIndep_of_wt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hAT : AllTest Xo c)
    (hU : IsUnf (U σ)) (hA : BCEx Xo c σ) (hF : WtField Xo c) : RdIndep Xo c U σ := by
  intro a k _ n b hb hli
  have hT : ∀ kk x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un kk x) := by
    intro kk x
    letI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    exact hAT (CAt σ) ((U σ).un kk x)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ kk (x : ((U σ).X kk).dom), ∑ i, g i * toC (evR Xo c (b i) ((U σ).un kk x)) = 0 := by
    intro kk x
    have h := congrFun (congrFun hg kk) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [← rdU_apply_dom (U σ) _ kk x]
  have hall := rel_of_frames (U σ) hU.2.2.1 hT hF b hb g hrel
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hc := indep_of_complex (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hW
    (fun p φ y => hA p y φ) b (fun i => (hb i).1) hli g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTieAsm
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory


theorem act_natCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (n : ℕ) : t.act.act (n : 𝓞 E) = 𝟙 _ ^ n := by
  have act0 : t.act.act 0 = 1 := by
    have h0 := t.act.add 0 0
    rw [add_zero] at h0
    exact mul_eq_left.1 h0.symm
  induction n with
  | zero => rw [Nat.cast_zero, act0, pow_zero]
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def SupAtUnitSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w,
      0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) →
      ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
        (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧
        supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤
          2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧
        0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 44 * large₂.sc.L

def CuspTieSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    LastPos (T.Q.Dw j) (wtA w) →
    ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f → f ∈ T.C j w

structure XExt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) where
  k0 : ℝ
  minWeight_pos : 0 < k0
  k0_le : k0 ≤ 2
  ξ0_abs : ∀ τ : X.Ψ, ‖τ.1 X.ξ0‖ = k0 / 2
  EF_int : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ k : ℤ, EFf X.ξ0 X.Gm x y = k
  EF_perf : ∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y
  L' : Submodule (𝓞 E) (Fin r → E)
  L'_fg : L'.FG
  L'_int : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)
  L'_dual : ∀ x, (∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)) → x ∈ L'
  NA : ℕ
  NC : ℕ
  NA_pos : 0 < NA
  NC_pos : 0 < NC
  NA_sub : ∀ x ∈ X.Λ, (NA : E) • x ∈ L'
  NC_sub : ∀ x ∈ L', (NC : E) • x ∈ X.Λ
  g : ℕ
  g_pos : 0 < g
  cong : ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ →
    (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ

def XExt.toX {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} (e : XExt X) :
    DataX E r :=
  ⟨X, e.k0, e.minWeight_pos, e.k0_le, e.ξ0_abs, e.EF_int, e.EF_perf, e.L', e.L'_fg, e.L'_int, e.L'_dual, e.NA, e.NC,
    e.NA_pos, e.NC_pos, e.NA_sub, e.NC_sub, e.g, e.g_pos, e.cong⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def FrBCFieldSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (K : Type) [Field K] [Algebra c.F K]
    (ψ : S →ₐ[c.F] K), ∃ z : FrPt Xo c K, FrMap ψ y z

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

