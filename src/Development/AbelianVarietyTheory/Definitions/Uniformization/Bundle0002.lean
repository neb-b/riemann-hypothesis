module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU

def AllPre (p : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegPre V}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G],
    PreU (IsLocalRing.maximalIdeal V) D A G → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V)
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    (U : PreU (IsLocalRing.maximalIdeal V) D A G), p U

abbrev TA (V W : Type) [CommRing V] [CommRing W] [Algebra V W] : Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))

abbrev Kbar (V : Type) [CommRing V] [IsDomain V] : Type := AlgebraicClosure (FractionRing V)

def FinExt (V W : Type) [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W] : Prop :=
  Module.Finite V W ∧ Module.Free V W ∧ IsDomain W ∧ IsLocalHom (algebraMap V W) ∧
    IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W

theorem finExt_self (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    (h : IsAdicComplete (IsLocalRing.maximalIdeal V) V) : FinExt V V := by
  have hmap : (IsLocalRing.maximalIdeal V).map (algebraMap V V) = IsLocalRing.maximalIdeal V := by
    rw [show algebraMap V V = RingHom.id V from rfl, Ideal.map_id]
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [show algebraMap V V = RingHom.id V from rfl]
    infer_instance
  · rw [hmap]
    exact h

theorem cdvr_padicInt (p : ℕ) [Fact p.Prime] : CDVR ℤ_[p] := by
  refine ⟨inferInstance, inferInstance, inferInstance⟩

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def PreU.PullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))}
    (φ : TF (R := R) F ⟶ T) (k : ℕ) (σ : U.SecGT T k) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : Prop :=
  ∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
    (rG : Z ⟶ (T ⊗ G).left), rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left →
    rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) → rG ≫ (fst T G).left = rA ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left →
    ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
      (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
          sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t rA z JA =
        sval σ rG z JG

def PullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))}
    (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) (s : Raw D F k) : Prop :=
  ∀ (α : D.X) (z : (DegPre.BF D F).left) (J), Good D.P.L z J →
    sval (s α) (𝟙 _) z J = sval (f α) (φ ▷ D.P.A).left z J

def PreU.SamePt (U : PreU I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A)
    (y : TF (R := R) F ⟶ G) : Prop := x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = y.left

def PreU.Supp (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Prop :=
  ∃ t s, U.ExpF F k t s ∧ ∃ j, (s α).f j ≠ 0

def PreU.FE (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : Prop :=
  ∀ t s, U.ExpF F k t s → DegPre.FamFE D F k s

def PreU.Acts (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (y : D.X) (g : GtPtF D F)
    (x : TFK (R := R) F ⟶ A.A) : Prop :=
  x ^ k = 1 ∧ ∀ θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F), θ.pt = x →
    ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k)), w.IsGen ∧
      ∀ t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → IsActOf A.A A.L (k : ℤ) θ t t' → PhiRaw D F k y g w s s'

def GtTors (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) : Prop :=
  ∃ h, GtPtF.IsNsmul k g h ∧ h.IsZero

def addε : Fin 10 → ℤ := ![1, 1, -1, 1, 1, -1, -1, 1, -1, 1]

end
end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU

def kap0 {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (x y : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  cubV c z J x y y⁻¹ * (val sym y.left z J)⁻¹ *
    val (L := L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) L.rig T.hom z J ^ 2
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

abbrev cT (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

def rigV (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T.left.presheaf.stalk z)ˣ := val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig T.hom z J

def kapV (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (x y : T ⟶ D.P.A) : (T.left.presheaf.stalk z)ˣ :=
  kap0 D.cub D.sym z J x y * cubV D.cub z J (cT D T a) (cT D T b) x * cubV D.cub z J (cT D T b) y y⁻¹ *
    (cubV D.cub z J (cT D T a) x y * cubV D.cub z J (cT D T b) x y⁻¹ * cubV D.cub z J (cT D T (a - b)) (cT D T b) y)⁻¹

def PreU.AddG (U : PreU I D A G) (θ : U.SecGT (𝟙_ _) 1) (r : R) {n : ℕ} (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ G) (z : T.left) (J), Good U.P.L.L z J →
    ∑ i, sval (σ i) (lift (toUnit T) x).left z J * sval (σ' i) (lift (toUnit T) y).left z J =
      gs (𝟙 _) z ⊤ (scal T.hom r) * (kap0 U.P.c U.P.sym z J x y).val *
        (sval θ (lift (toUnit T) (x * y)).left z J * sval θ (lift (toUnit T) (x * y⁻¹)).left z J)

def AddB (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (f₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (f f' : Fin n → ∀ α, SecBT D T₀ 2 α) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
    (∀ a b α β : D.X, α = a + b → β = a - b →
      ∑ i, sval (f i α) (lift ρ x).left z J * sval (f' i β) (lift ρ y).left z J =
        gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
          (sval (f₀ a) (lift ρ (x * y)).left z J * sval (f₀ b) (lift ρ (x * y⁻¹)).left z J)) ∧
    ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) →
      ∑ i, sval (f i α) (lift ρ x).left z J * sval (f' i β) (lift ρ y).left z J = 0

def PreU.Theta (U : PreU I D A G) (θ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) : Prop :=
  U.ExpT (𝟙_ _) 1 θ f ∧ ∃ j, θ.f j ≠ 0

def PsiRel (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (f : ∀ α, SecBT D T₀ 1 α) : Prop :=
  ∀ (χ : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (y : T ⟶ D.P.A) (z : T.left) (J),
    Good D.P.L z J → sval (f χ) (lift ρ y).left z J =
      (val (D.psi χ) κ.left z J * rigV D z J).val * sval (f 0) (lift ρ (y * cT D T χ)).left z J

def setPsi (D : DegPre R)
    (ψ : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1))) (h : ∀ χ, (ψ χ).IsGen) :
    DegPre R := { D with psi := ψ, psi_gen := h }

def PsiScal (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) : Prop :=
  ∀ χ, (ga χ).IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (κ : T ⟶ TK R) (z : T.left) (J), Good D.P.L z J →
    (val (D.psi χ) κ.left z J).val = gs (𝟙 _) z ⊤ (scal κ.left (a χ).val) * (val (ga χ) (toUnit T).left z J).val
end

def AddA {S : Scheme.{0}} (P : PolAV S) (T₀ : Over S) (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T₀)) {n : ℕ}
    (t t' : Fin n → LB.Sec (LPow P.A P.L ((2 : ℕ) : ℤ) T₀)) : Prop :=
  ∃ κ : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(snd T₀ (P.A ⊗ P.A) ≫ fst P.A P.A).left, (snd T₀ (P.A ⊗ P.A) ≫ snd P.A P.A).left,
        (snd T₀ (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A)).left,
        (snd T₀ (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹)).left] ![2, 2, -1, -1]), κ.IsGen ∧
    ∀ (T : Over S) (ρ : T ⟶ T₀) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t i) (lift ρ x).left z J *
          sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t' i) (lift ρ y).left z J =
        (val κ (lift ρ (lift x y)).left z J).val *
          (sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th (lift ρ (x * y)).left z J *
            sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th (lift ρ (x * y⁻¹)).left z J)

abbrev EA {S : Scheme.{0}} (P : PolAV S) {F : Type} [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) : Type :=
  SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L (k : ℤ) (Over.mk p))

abbrev WB {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (α : D.X) : Type :=
  SecMod (F := F) (fst (TF (R := R) F) D.P.A).left (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))
end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

structure Match (U : PreU I D.toPre A G) (U' : UnifPre I D A G) : Prop where
  gen : U'.gen = U.gen
  LG : U'.LG = U.P.L
  cub : HEq U'.cubG U.P.c
  sym : HEq U'.symG U.P.sym
  gt : U'.gt = U.gt
  w : HEq U'.w U.w

def SameG {L : LB G.left} {k : ℕ} (σ : H0 L k)
    (σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ G).left) (z : Z) (J), Good L z J →
    sval σ' r z J = sval σ (r ≫ (snd _ G).left) z J

def SameB {D : DegPre R} {k : ℕ} (f : ∀ α, D.SecB k α) (f' : ∀ α, SecBT D (𝟙_ _) k α) : Prop :=
  ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval (f' α) r z J = sval (f α) (r ≫ (snd _ D.P.A).left) z J

def PreU.SameK {D : DegPre R} (U : PreU I D A G) {k : ℕ}
    (σ : LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) (FractionRing R)))) : Prop :=
  ∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) (FractionRing R) ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left),
    rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left → ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
      (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
          sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) (FractionRing R)) A.A).left) (ε := fun _ => (k : ℤ)) t rA z JA =
        sval σ y z JG
end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UT.Cl
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def Torsion (U : Unif I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (k : ℕ), 1 ≤ k → ∃ f, Tors U.toUnifPre F k f ∧ ∀ p, f p ^ k = 1

def Galois (U : Unif I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (F' : Type) [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (k : ℕ), 1 ≤ k →
    ∀ p : QkPt D.toPre F k, (∃ p' : QkPt D.toPre F' k, QkExt σ.toRingHom p p') ∧
      (∀ x : TFK (R := R) F ⟶ A.A, ∃ x' : TFK (R := R) F' ⟶ A.A, x'.left = spMap σ.toRingHom ≫ x.left) ∧
      ∀ (p' : QkPt D.toPre F' k) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R) F' ⟶ A.A), QkExt σ.toRingHom p p' →
        x'.left = spMap σ.toRingHom ≫ x.left → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F' k p' x')

def SymFrame (U : Unif I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (N : ℕ), Odd N → ∀ p : QkPt D.toPre F N,
    ((∃ w, TXFrame N p w) ∧ ∀ w w', TXFrame N p w → TXFrame N p w' →
      ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J) ∧
    ∀ x, QkToAkU U.toUnifPre F N p x → (∃ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F), SymLift A.A A.L N N x θ) ∧
      ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen →
        ∀ w, TXFrame N p w → ∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' →
          PhiRel D.toPre F N p w s s'

def Functorial (U : Unif I D A G) : Prop :=
  (∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA) ∧
  ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) →
    (RosatiAdj A.A A.L E.aA E'.aA ∧ RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB ∧
      (∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB) ∧ ∀ χ, D.toPre.c (E'.h χ) = D.toPre.c χ ≫ E.aB) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], (∀ g : GtPtF D.toPre F, ∃! g', E.Act g g') ∧
      (∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g') ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x, p'.y = E'.h p.y → E.Act p.g p'.g → QkToAkU U.toUnifPre F k p x →
        QkToAkU U.toUnifPre F k p' (x ≫ E.aA)

def Determined (U : Unif I D A G) : Prop :=
  ∀ (D' : DegData R I) (A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G' : Over (Spec (CommRingCat.of R))) [GrpObj G']
    [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre),
    ∃ (ψ : G' ≅ G) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (φ : A'.A ≅ A.A), IsMonHom ψ.hom ∧ IsMonHom bc.hom ∧
      bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left ∧ IsPullUnif (RingHom.id R) hD bc U U' ∧
      IsMonHom φ.hom ∧ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom = U'.gen.hom ≫ φ.hom ∧ LBIso A'.L (A.L.pull φ.hom.left)

def Balanced (U : Unif I D A G) : Prop :=
  (∀ (O : Type) [CommRing O] [StarRing O] (ιA : A.OAct O) (ιG : RingAct G O), (∀ a, (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a) → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∃ (_ : Module O D.toPre.X) (ιD : D.toPre.OAct O), U.toUnifPre.OLinear O ιD ιA ιG) ∧
  ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O) (ν : ℕ), w₀ + star w₀ = 1 → w₀ * star w₀ = (ν : O) → 1 ≤ ν → Even ν → LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → TraceFormTwistIso D.toPre ιD w₀
end

end GlobalTheory.UT.Cl
end
end

