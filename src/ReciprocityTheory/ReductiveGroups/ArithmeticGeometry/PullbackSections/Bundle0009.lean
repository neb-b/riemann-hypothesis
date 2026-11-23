module

public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) := RingHom.ext fun x => by ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem frMap_refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have e : dualMap (AlgHom.id c.F S).toRingHom = RingHom.id _ :=
    RingHom.ext fun x => by ext <;> simp [dualMap]
  refine ⟨?_, ?_, 𝟙 _, ?_, ?_, ?_⟩
  · rw [spMap_algHom_id, Category.id_comp]
  · intro τ i
    rw [e]
    simp [spMap]
  · exact Category.id_comp _
  · rw [spMap_algHom_id]
    simp
  · intro i h
    rw [show Scheme.Hom.appLE (𝟙 (Gx y.x)) _ _ h = Scheme.Hom.app (𝟙 (Gx y.x)) ((PPx y.x).U i) from
      (Scheme.Hom.app_eq_appLE _).symm, Scheme.Hom.id_app]
    rfl

theorem frMap_trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  have hc : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := rfl
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, hc, spMap_comp, Category.assoc]
  · intro τ i
    rw [hu2, hu1, hc, dualMap_comp, spMap_comp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, Category.assoc, ← spMap_comp, hc]
  · intro i h
    have hb1 : ∀ p, (snd (Over.mk y.x) Xo.univ.t.G).left.base (pm1.base p) =
        (snd (Over.mk z.x) Xo.univ.t.G).left.base p := fun p => by
      rw [← hs1]; rfl
    have hb2 : ∀ p, (snd (Over.mk z.x) Xo.univ.t.G).left.base (pm2.base p) =
        (snd (Over.mk w.x) Xo.univ.t.G).left.base p := fun p => by
      rw [← hs2]; rfl
    have h1 : (PPx z.x).U i ≤ pm1 ⁻¹ᵁ (PPx y.x).U i := by
      intro p hp
      change p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp
      change pm1.base p ∈ (⋂ k, (snd (Over.mk y.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))
      simp only [Set.mem_iInter, Set.mem_preimage] at hp ⊢
      intro k
      rw [hb1]
      exact hp k
    have h2 : (PPx w.x).U i ≤ pm2 ⁻¹ᵁ (PPx z.x).U i := by
      intro p hp
      change p ∈ (⋂ k, (snd (Over.mk w.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp
      change pm2.base p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))
      simp only [Set.mem_iInter, Set.mem_preimage] at hp ⊢
      intro k
      rw [hb2]
      exact hp k
    rw [← Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1 h2]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [ha1 i h1, ha2 i h2]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

def cpθ : ChartPull (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (PPx x) (gxU x) :=
  (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk x) Xo.univ.t.G).left).cp
    (PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)) (gxU x) (gxU_snd x)

def cpV : ChartPull (PPx x) (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (gxV x) :=
  (PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).cp
    (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk x) Xo.univ.t.G).left) (gxV x) (gxV_fst x)

def cpσ : ChartPull ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ)))
    (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (pullback.fst _ (spMap ψ)) :=
  chartPullPull _ _ _ rfl

def cpU' : ChartPull ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ))) (PPx (spMap ψ ≫ x)) (bcU ψ x) :=
  (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left).cp
    ((PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).pull _) (bcU ψ x) (bcU_snd ψ x)

def cpV' : ChartPull (PPx (spMap ψ ≫ x)) ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ))) (bcV ψ x) :=
  ((PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).pull _).cp
    (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left) (bcV ψ x)
    (bcV_snd' ψ x)

def cpS : ChartPull (PPx (spMap ψ ≫ x)) (PPx x) (bcPm ψ x) :=
  cpSame Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
    (fun _ => (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left) (fun _ => 1) (bcPm ψ x) (fun _ => bcPm_snd ψ x)

def tA : SAB H (Sp S) := sabT ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt x Xo.univ.t
def mA : SABMap (tA x) Xo.univ.t x := sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt x Xo.univ.t

def tB : SAB H (Sp T) := sabT ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap ψ) (tA x)
def mB : SABMap (tB ψ x) (tA x) (spMap ψ) := sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap ψ) (tA x)

def θA (s0 : LB.Sec (PPx x)) : LB.Sec (tA x).PP.L := secCP (cpθ x) s0

def σB (s0 : LB.Sec (PPx x)) : LB.Sec (tB ψ x).PP.L := secCP (cpσ ψ x) (θA x s0)

theorem hθ_of (s0 : LB.Sec (PPx x)) (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i)
    (σ : LB.Sec (tA x).PP.L) : ∃ a : S, ∀ i, σ.f i = constFn (tA x).G.hom _ a * (θA x s0).f i := by
  obtain ⟨a, ha, -⟩ := hgen (secCP (cpV x) σ)
  refine ⟨a, (sec_eq_iff _ σ (θA x s0) a).2 fun i q hq => ?_⟩
  have hJ : gxU x q ∈ (PPx x).U (fun _ => i PUnit.unit) := (cpθ x).le i hq
  have h2 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (gxU x) q hJ ((scal_eq_iff x _ _ a).1 ha _ (gxU x q) hJ)
  rw [gs_secCP (cpV x) σ (gxU x) q _ hJ, gxU_gxV, gxU_fst] at h2
  have e3 : gs (𝟙 _) q ((tA x).PP.L.U i) ((θA x s0).f i) =
      gs (gxU x) q ((PPx x).U (fun _ => i PUnit.unit)) (s0.f (fun _ => i PUnit.unit)) :=
    (gs_secCP (cpθ x) s0 (𝟙 _) q i hq).trans (by rw [Category.id_comp]; rfl)
  rw [e3]
  exact h2

theorem hσ_of (s0 : LB.Sec (PPx x)) (y : (tB ψ x).G.left) (j : PUnit → Xo.univ.t.PP.L.ι)
    (k : PUnit → PUnit → Xo.univ.t.PP.L.ι) (hj : (mB ψ x).φ y ∈ (tA x).PP.L.U j) (hk : y ∈ (tB ψ x).PP.L.U k) :
    gs (mB ψ x).φ y _ ((θA x s0).f j) =
      (gw (idIso ((tA x).PP.L.pull (mB ψ x).φ)) (𝟙 _) y j k).val * gs (𝟙 _) y _ ((σB ψ x s0).f k) := by
  have hk' : (mB ψ x).φ y ∈ (tA x).PP.L.U (k PUnit.unit) := mem_pull.1 hk
  have e1 := gm_pull_g (tA x).PP.L (mB ψ x).φ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hk
  rw [Category.id_comp] at e1
  have e2 : gs (𝟙 _) y ((tB ψ x).PP.L.U k) ((σB ψ x s0).f k) =
      gs (mB ψ x).φ y ((tA x).PP.L.U (k PUnit.unit)) ((θA x s0).f (k PUnit.unit)) :=
    (gs_secCP (cpσ ψ x) (θA x s0) (𝟙 _) y k hk).trans (by rw [Category.id_comp]; rfl)
  rw [e2, gs_compat (θA x s0) (mB ψ x).φ y hj hk']
  exact congrArg (· * _) (congrArg Units.val e1.symm)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Mixed

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

abbrev endT (T : Over X) (φ : A ⟶ A) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ φ)

def IsNormEnd (φ : A ⟶ A) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) : Prop :=
  LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (eSec A))
    (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))

def IsMixedOver (φ : A ⟶ A) (n k : ℕ) {T : Over X} (ok : (T ⟶ A) → Prop) (s : LB.Sec (LPow A L.L 1 T))
    (t₁ b : T ⟶ A) (hh : LB.Sec (LPow A L.L (k : ℤ) T)) : Prop :=
  ∃ (F₁ : LB.Sec (LPow A L.L ((n : ℤ) ^ 2) T))
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (h₁ : LB.Sec (LPow A L.L (k : ℤ) T)) (U : ThetaGrp A L.L (k : ℤ) T),
    IsVtOver A L n ok s t₁ F₁ ∧ α₀.IsGen ∧ IsNormEnd A L φ (k : ℤ) ((n : ℤ) ^ 2) α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (endT A T φ) (snd T A ≫ φ) (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ ∧
    SymLift A L.L (k : ℤ) k b U ∧ IsActOf A L.L (k : ℤ) U h₁ hh

end Mixed

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


open Classical in
theorem rdU_apply_dom {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f : Rul Xo c) (k : U.Comp) (x : (U.X k).dom) : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := by
  show (if h : x.1 ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0) = _
  rw [dite_eq_left x.2]

theorem rel_of_frames {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hU3 : ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (U.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) y)
    (hT : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x))
    (hF : WtField Xo c) {m : ℕ} (fs : Fin m → Rul Xo c) (hfs : ∀ i, fs i ∈ sec Xo c a n) (g : Fin m → ℂ)
    (hrel : ∀ k (x : (U.X k).dom), ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) = 0)
    (z : FrPt Xo c (CAt σ)) (hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z) :
    ∑ i, g i * toC (evR Xo c (fs i) z) = 0 := by
  obtain ⟨k, x, t, hbor⟩ := hU3 z
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hv : ∀ i, evR Xo c (fs i) z = wchar (ex Dw a n) t * evR Xo c (fs i) (U.un k x) :=
    fun i => hF a n (fs i) (hfs i) (CAt σ) t _ z (hT k x) hz hbor
  calc ∑ i, g i * toC (evR Xo c (fs i) z)
      = ∑ i, g i * (toC (wchar (ex Dw a n) t) * toC (evR Xo c (fs i) (U.un k x))) :=
        Finset.sum_congr rfl fun i _ => by rw [hv i]; rfl
    _ = toC (wchar (ex Dw a n) t) * ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hrel k x, mul_zero]

end Frames

theorem jInjRd_of_wt {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hA : BCEx (T.Q.Xo j) T.Q.c T.σ₀) (hF : WtField (T.Q.Xo j) T.Q.c) :
    JInjRd T j a n := by
  intro m b hb
  have hU : IsUnf (T.U j T.σ₀) := hM.unf j hj T.σ₀ T.good_σ₀
  set_option synthInstance.maxHeartbeats 200000 in
  have hb' := hb.map' (cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype (Submodule.ker_subtype _)
  have hfs : ∀ i, (⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i ∈ sec (T.Q.Xo j) T.Q.c a n :=
    fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (b i).2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ k (x : ((T.U j T.σ₀).X k).dom),
      ∑ i, g i * toC (evR (T.Q.Xo j) T.Q.c ((⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i)
        ((T.U j T.σ₀).un k x)) = 0 := by
    intro k x
    have h := congrFun (congrFun hg k) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← rdU_apply_dom (T.U j T.σ₀) _ k x]; rfl
  have hall := rel_of_frames (T.U j T.σ₀) hU.2.2.1 (hM.unTest j hj T.σ₀ T.good_σ₀) hF _ hfs g hrel
  let _ : Algebra T.Q.c.F ℂ := T.σ₀.toAlgebra
  have hc := indep_of_complex (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S)
    (fun φ y z => FrMap φ y z) (hM.evalWD j hj) (fun p φ y => hA p y φ)
    _ (fun i => (hfs i).1) hb' g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeD
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {x : Sp S ⟶ Xo.X}

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM x Xo.univ.t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => first | rfl | simp [tv]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, tv_add, ih]

variable {c}

def tvOf {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : TanM x Xo.univ.t.G :=
  mkT (ovT (t := Xo.univ.t) hv) (smT_zero_ovT hv)

theorem tv_tvOf {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : tv (tvOf hv) = ovT (t := Xo.univ.t) hv := rfl

variable (c) in
theorem eigAt_iff {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (τ : E →+* ℂ) :
    IsEigAt (c := c) τ v ↔ IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (tvOf hv) := by
  refine (isEigAt_iff (c := c) τ (ovT (t := Xo.univ.t) hv)).trans ?_
  constructor
  · intro h a
    apply tanM_ext
    show tv (tvOf hv) ≫ Xo.univ.t.act.act a = _
    rw [tv_smul, tv_tvOf]
    exact h a
  · intro h a
    have h2 := congrArg tv (h a)
    change tv (tvOf hv) ≫ Xo.univ.t.act.act a = _ at h2
    rw [tv_smul, tv_tvOf] at h2
    exact h2

theorem combAt_iff {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ i, IsTanAt x (u i))
    (cf : Fin m → S) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x w) :
    IsCombAt x u cf w ↔ tvOf hw = ∑ i, cf i • tvOf (hu i) := by
  have e1 : tv (∑ i, cf i • tvOf (hu i)) = combT x (fun j => ovT (t := Xo.univ.t) (hu j)) cf := by
    rw [tv_sum]
    simp only [tv_smul, tv_tvOf]
    rfl
  have key := isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hu j)) cf w
  constructor
  · intro h
    apply tanM_ext
    rw [e1, tv_tvOf]
    exact Over.OverMorphism.ext (key.1 h).symm
  · intro h
    have h2 := congrArg tv h
    rw [e1, tv_tvOf] at h2
    exact key.2 (by rw [← h2]; rfl)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GamAt {D : D7} (T : Top D) : Prop :=
  ∀ (j : ℕ) (_hj : InR D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (γ : GL (Fin D.R.r) D.host.E), IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ →
    (∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y) →
    γ ∈ ((T.U j σ).X k).Γ

def HalfDiffNormSt : Prop :=
  ∀ D : D7, 0 < Ideal.absNorm D.host.𝔟 ∧
    2 * Real.log (Ideal.absNorm D.host.𝔟 : ℝ) ≤ Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)|

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PPSemichar
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj MonObj
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem hermForm_zero_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  unfold hermForm
  simp

theorem hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  rw [add_dotProduct]

theorem hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hji : star (Hm i j) = Hm j i := by
    have := congrFun (congrFun hH j) i
    rwa [Matrix.conjTranspose_apply] at this
  simp only [Pi.star_apply, star_star, hji]
  ring

theorem hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (t • z) w = t * hermForm Hm z w := by
  unfold hermForm
  rw [smul_dotProduct, smul_eq_mul]

theorem hermForm_real_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z ((t : ℂ) • w) = t * hermForm Hm z w := by
  unfold hermForm
  have h1 : star ((t : ℂ) • w) = (t : ℂ) • star w := by
    ext i
    simp [Complex.conj_ofReal]
  rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

section Prim

variable {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)

end Prim

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TanAddPf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem tanAdd_holds (Xo : Moduli Dw l) : TanAddSt Xo := by
  intro S _ x w hw a b u₁ u₂ h₁ h₂
  have e₁ : u₁ = smT x a (ovT (t := Xo.univ.t) hw) := Over.OverMorphism.ext h₁
  have e₂ : u₂ = smT x b (ovT (t := Xo.univ.t) hw) := Over.OverMorphism.ext h₂
  rw [e₁, e₂, ← smT_add x _ (smT_zero_ovT hw)]
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

