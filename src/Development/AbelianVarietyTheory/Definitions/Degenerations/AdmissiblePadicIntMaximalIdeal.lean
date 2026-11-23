module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev CDvr (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] : Prop := GlobalTheory.UU.CDVR V

theorem cDvr_iff (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] :
    CDvr V ↔ IsDiscreteValuationRing V ∧ IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ CharZero V := Iff.rfl

def admitted (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) : Prop :=
  AdmBase R I ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧ CharZero R ∧ I.IsPrime ∧ IsIntegrallyClosed (R ⧸ I)

def PolAt {S : Scheme.{0}} (t : SAB H S) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  IsProper (pullback.snd t.G.hom x) ∧ RelAmple ((Over.pullback x).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom x)) ∧
    KTriv ((Over.pullback x).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom x))

def SplitOver {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] (I : Ideal R) : Prop :=
  ∃ S : SplitExt (Sp (R ⧸ I)), S.IsGt ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj G)

def ThetaNZ {S : Scheme.{0}} (G : Over S) (L : LB G.left) : Prop :=
  ∃ θ : L.Sec, ∀ y : S, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ.f i)

def UDvrSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
  (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ t : SAB H (Sp V), PolAt t (jK V) →
  SplitOver t.G (IsLocalRing.maximalIdeal V) → ∃ P : PELUnif (IsLocalRing.maximalIdeal V) t, P.TorsionIso

def Lin {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) (c : Fin n → Γ(T'.left, ⊤)) (s : LB.Sec (LPow G L (N : ℤ) T')) : Prop :=
  ∀ (z : (T' ⊗ G).left) (J), Good L z J →
    sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s (𝟙 _) z J =
      ∑ i, gs (fst T' G).left z ⊤ (c i) *
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J

def BasisAlong {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) : Prop :=
  (∀ s, ∃! c, Lin G L N h b c s)

def IsFrame {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {R₁ : Type} [CommRing R₁] [IsDomain R₁]
    (x : Sp (FractionRing R₁) ⟶ S) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W),
    (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ (χ : Sp W ⟶ S) (h : spMap gam ≫ x = jK W ≫ χ),
    ∃ b' : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk χ)), BasisAlong G L N (𝟙 _) b' ∧
      ∀ i, ∃ s : LB.Sec (LPow G L (N : ℤ) (Over.mk (jK W ≫ χ))),
        Lin G L N (Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) (fun _ : Fin 1 => b i) (fun _ => 1) s ∧
        Lin G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) (fun _ : Fin 1 => b' i) (fun _ => 1) s

structure AmpFrames {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) where

  A : LB Z

  isLB : A.IsLB

  ample : ∀ z : Z, ∃ (d : ℕ) (s : H0 A d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)

  n : ℕ

  th : ∀ i : A.ι, LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk (A.U i).ι))

  b : ∀ i : A.ι, Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (A.U i).ι))

  r : ℤ

  s : ℤ

  trans : ∀ i j : A.ι, ∃ (c : Γ((A.U i ⊓ A.U j).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((A.U i ⊓ A.U j).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => th i) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (fun _ : Fin 1 => th j) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => b i k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (b j) (fun k' => M.val k k') t) ∧
    (A.U i ⊓ A.U j).topIso.inv.hom (A.g i j).val = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val

  trait : ∀ (i : A.ι) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ χ : Sp W ⟶ (A.U i).toScheme,
    Set.range (jK W ≫ χ ≫ (A.U i).ι) ⊆ abLocus G →
    BasisAlong G L 1 (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (fun _ : Fin 1 => th i) ∧
    BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (b i)
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def Amp (Y : Model Xo c β) : Prop :=
  ∃ (m : ℕ) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), Odd m ∧ IsUnit (m : O) ∧ IsFinite π ∧
    Surjective π ∧ Nonempty (AmpFrames t.G t.PP.L (m ^ 2))

def ArcBase (O' : Type) [CommRing O'] [IsDomain O'] (ϖ : O') : Prop :=
  (IsField O' ∧ ϖ = 1) ∨ (IsDiscreteValuationRing O' ∧ Irreducible ϖ ∧ IsAdicComplete (Ideal.span {ϖ}) O')

def TraitData (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b)
    {R₁ : Type} [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) : Prop :=
  y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b ∧
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W),
    (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ χ : Sp W ⟶ Y.X, spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ →
    (IsUnit (φ (g PowerSeries.X)) → Set.range χ ⊆ abLocus Y.t.G) ∧
    (¬ IsUnit (φ (g PowerSeries.X)) → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W'),
      CDvr W' ∧ Function.Injective io ∧ io.Finite ∧
      Y.HasArcData a (IsLocalRing.maximalIdeal W') (io.comp (φ.comp (g.comp (PowerSeries.C (R := O'))))) (io (φ (g PowerSeries.X)))
        (spMap io ≫ χ))

namespace Frames

variable {Z : Scheme.{0}} (G : Over Z) (A : LB Z) (N : ℕ)

theorem snd_hom (T : Over Z) : (snd T G).left ≫ G.hom = (fst T G).left ≫ T.hom :=
  (Over.w (snd T G)).trans (Over.w (fst T G)).symm

theorem whisker_snd {T T' : Over Z} (h : T' ⟶ T) : (h ▷ G).left ≫ (snd T G).left = 𝟙 _ ≫ (snd T' G).left := by
  rw [Category.id_comp, ← Over.comp_left, whiskerRight_snd]

end Frames

end GlobalTheory.LN
end
