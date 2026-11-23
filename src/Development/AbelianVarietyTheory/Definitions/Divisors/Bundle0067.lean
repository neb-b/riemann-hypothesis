module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTensElliptic
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.TraitWit

open GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem comp_tensφ {S : Scheme.{0}} {B B' T : Over S} [GrpObj B] {r : ℕ} (pr : Fin r → (B' ⟶ B)) (x : T ⟶ B')
    (k : (Fin r × Fin r) × Fin 4) : x.left ≫ tensφ pr k = lamPts (x ≫ pr k.1.1) (x ≫ pr k.1.2) k.2 := by
  obtain ⟨⟨i, j⟩, k⟩ := k
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul x (pr i) (pr j))
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := B) x)

theorem formula_trans (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left}
    (pr : Fin r → (B' ⟶ D.P.A)) {w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → D.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ D.c (y i)) (z : (TK R).left) (J J₀) (hJ : Good D.P.L z J)
    (hJ₀ : Good D.P.L z J₀) (k k₀ : L'.ι) (hk : x.left z ∈ L'.U k) (hk₀ : x.left z ∈ L'.U k₀) :
    gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), k)) * ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j =
      (gm x.left z _ (L'.g k k₀))⁻¹ * (gm x.left z _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), k₀)) *
        ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J₀ ^ W i j) := by
  let H : ((TK R).left ⟶ D.P.A.left) → ((TK R).left.presheaf.stalk z)ˣ := fun ψ => gm ψ z _ (D.P.L.g (J ψ) (J₀ ψ))
  let F : Fin r → Fin r → ((TK R).left.presheaf.stalk z)ˣ := fun i j =>
    ∏ a, H (lamPts (toUnit (TK R) ≫ D.c (y i)) (toUnit (TK R) ≫ D.c (y j)) a) ^ Oε a
  have h₁ : gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), k)) =
      gm x.left z _ ((LB.LinComb D.P.L (tensφ pr) (tensε W)).g
        (fun a => J (x.left ≫ tensφ pr a)) (fun a => J₀ (x.left ≫ tensφ pr a))) *
      (gm x.left z _ (L'.g k k₀))⁻¹ *
      gm x.left z _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), k₀)) := by
    have hm : x.left z ∈ (LB.LinComb D.P.L (tensφ pr) (tensε W)).U (fun a => J (x.left ≫ tensφ pr a)) ⊓ L'.U k ⊓
        ((LB.LinComb D.P.L (tensφ pr) (tensε W)).U (fun a => J₀ (x.left ≫ tensφ pr a)) ⊓ L'.U k₀) :=
      ⟨⟨hJ.mem (tensφ pr) x.left, hk⟩, hJ₀.mem (tensφ pr) x.left, hk₀⟩
    have e := congrArg (gm x.left z _) (hw (fun a => J (x.left ≫ tensφ pr a), k)
      (fun a => J₀ (x.left ≫ tensφ pr a), k₀))
    exact (gm_res x.left z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_div L' _ x.left z _ _ hm) (gm_res x.left z _ hm _))))
  have h₂ : gm x.left z _ ((LB.LinComb D.P.L (tensφ pr) (tensε W)).g (fun a => J (x.left ≫ tensφ pr a))
      (fun a => J₀ (x.left ≫ tensφ pr a))) = ∏ i, ∏ j, F i j ^ W i j := by
    refine (gm_linComb D.P.L (tensφ pr) (tensε W) x.left z _ _ (hJ.mem (tensφ pr) x.left) (hJ₀.mem (tensφ pr) x.left)).trans ?_
    change ∏ a, H (x.left ≫ tensφ pr a) ^ tensε W a = _
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [comp_tensφ, hx, hx, ← zpow_mul, mul_comm]
    rfl
  have h₃ : ∀ i j, val (D.tau (y i) (y j)) (𝟙 _) z J = (F i j)⁻¹ * val (D.tau (y i) (y j)) (𝟙 _) z J₀ := fun i j => by
    obtain ⟨t, ht, hv⟩ := exists_tau_four D (y i) (y j)
    refine (hv _ _ z J hJ).symm.trans ((gen_trans ht (𝟙 _) z (hJ.mem _ _) (hJ₀.mem _ _)).trans
      (congrArg₂ (· * ·) ?_ (hv _ _ z J₀ hJ₀)))
    change ∏ a, H (𝟙 _ ≫ lamPts (toUnit (TK R) ≫ D.c (y i)) (toUnit (TK R) ≫ D.c (y j)) a) ^ negε a = _
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Category.id_comp, ← zpow_neg]
    congr 1
    fin_cases a <;> rfl
  refine (congrArg₂ (· * ·) (h₁.trans (congrArg (· * _ * _) h₂)) (Finset.prod_congr rfl fun i _ =>
    Finset.prod_congr rfl fun j _ => congrArg (· ^ W i j) (h₃ i j))).trans ?_
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_psi (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left} (hL : L'.IsLB)
    (pr : Fin r → (B' ⟶ D.P.A)) {w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → D.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ D.c (y i)) :
    ∃ t : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => x.left) (fun _ => -1)), t.IsGen ∧
      ∀ z J J', Good D.P.L z J → Good L' z J' → val t (𝟙 _) z J' =
        gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), J' x.left)) *
          ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  let z₀ : (TK R).left := closedPoint (FractionRing R)
  obtain ⟨J₀, hJ₀, -⟩ := exists_good _ D.P.isLB z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J₁, hJ₁, -⟩ := exists_good _ hL z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨t, ht, hv⟩ := exists_gen_val (F := FractionRing R) hL (K := PUnit) (fun _ => x.left) (fun _ => -1) hJ₁
    (gm x.left z₀ _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), J₁ x.left)) *
      ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z₀ J₀ ^ W i j)
  refine ⟨t, ht, fun z J J' hJ hJ' => ?_⟩
  obtain rfl : z = z₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
  have a := gen_trans ht (𝟙 (TK R).left) z₀ (hJ'.mem (fun _ : PUnit => x.left) _) (hJ₁.mem (fun _ : PUnit => x.left) _)
  have b : trF (L := L') (fun _ : PUnit => x.left) (fun _ => -1) (𝟙 (TK R).left) z₀ (fun _ => J' (𝟙 _ ≫ x.left))
      (fun _ => J₁ (𝟙 _ ≫ x.left)) = (gm x.left z₀ _ (L'.g (J' x.left) (J₁ x.left)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp]
  exact (a.trans (congrArg₂ (· * ·) b hv)).trans
    (formula_trans D W pr hw x y hx z₀ J J₀ hJ hJ₀ (J' x.left) (J₁ x.left) (hJ' _) (hJ₁ _)).symm

end GlobalTheory.Mum.TraitWit
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwFam

variable {R : Type} [CommRing R] [IsDomain R]

def tφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) : Fin 5 → (D.P.A.left ⟶ D.P.A.left) :=
  ![𝟙 _, (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c β)).left, (toUnit D.P.A ≫ D.c β).left,
    (toUnit D.P.A ≫ η[D.P.A]).left, a.left]

def tε (n j : ℤ) : Fin 5 → ℤ := ![n - 1, 1, -1, 1, j]

abbrev SecT (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (tφ D a β) (tε n j))

def Van (I : Ideal R) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb D.P.L φ ε)) (e : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval s (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J = 0

def Small (I : Ideal R) {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) : Prop :=
  ∀ e : ℕ, {i | ¬ Van I (s i) e}.Finite

def dφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) (mu β β' : D.X) :
    Fin 5 ⊕ Fin 5 → ((DegPre.BF D (FractionRing R)).left ⟶ D.P.A.left) :=
  Sum.elim (fun k => (DegPre.prB D (FractionRing R)).left ≫ tφ D a β' k)
    (fun k => (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left ≫ tφ D a β k)

def dε (n j : ℤ) : Fin 5 ⊕ Fin 5 → ℤ := Sum.elim (tε n j) (fun k => - tε n j k)

def IsFac (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) (n j : ℤ) (mu β β' : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β') (dε n j))) : Prop :=
  u.IsGen ∧ ∀ (z : (TF (R := R) (FractionRing R)).left) (J), Good D.P.L z J →
    val u (DegPre.zF D (FractionRing R)).left z J =
      val (D.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j *
        val (D.tau mu β) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)

def TRel {D : DegPre R} {a : D.P.A ⟶ D.P.A} (h : D.X →+ D.X) {n j : ℤ} (mu : D.X) {β β' : D.X}
    (s : SecT D a n j β) (s' : SecT D a n j β') : Prop :=
  ∀ u, IsFac D a h n j mu β β' u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J),
    Good D.P.L z J → sval s' (x ≫ (DegPre.prB D (FractionRing R)).left) z J =
      sval s (x ≫ (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left) z J * (val u x z J).val

def shift {X : Type} [AddCommGroup X] (h h' : X →+ X) (n j : ℤ) (mu : X) : X := n • mu + j • h' (h mu)

def TFE {D : DegPre R} {a : D.P.A ⟶ D.P.A} (h h' : D.X →+ D.X) {n j : ℤ} (f : ∀ β, SecT D a n j β) : Prop :=
  ∀ mu β, TRel h mu (f β) (f (β + shift h h' n j mu))


open Classical in
def IsSum (I : Ideal R) {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) (F : ∀ δ, SecT D a n j δ) : Prop :=
  ∀ (e : ℕ) (S : Finset Ix), (∀ i ∉ S, Van I (s i) e) → ∀ (δ : D.X) (Z : Scheme.{0})
    (x : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval (F δ) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J =
        ∑ i ∈ S.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J

def IsProdT {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j n' j' n'' j'' : ℤ} {β β' : D.X} (f : SecT D a n j β)
    (g : SecT D a n' j' β') (p : SecT D a n'' j'' (β + β')) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
    sval p x z J = sval f x z J * sval g x z J *
      (val D.cub.t (x ≫ (lift (toUnit _ ≫ D.c β) (lift (toUnit _ ≫ D.c β') (𝟙 D.P.A)) : D.P.A ⟶ G3 D.P.A).left) z J).val

abbrev IotaLB (D : DegPre R) (a : D.P.A ⟶ D.P.A) (α δ : D.X) : LB D.P.A.left :=
  LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a α)) (Sum.elim Oε Oinvε)

def IsIota {D : DegPre R} {a : D.P.A ⟶ D.P.A} {α δ : D.X} (u : LB.Gen (IotaLB D a α δ)) : Prop :=
  u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.P.L z J → val u (r ≫ eSec D.P.A) z J = 1

def IsPullT {D : DegPre R} {a : D.P.A ⟶ D.P.A} {k : ℕ} {α δ : D.X} (u : LB.Gen (IotaLB D a α δ)) (f : D.SecB k α)
    (s : SecT D a 0 k δ) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
    sval s x z J = sval f (x ≫ a.left) z J * (val u x z J).val

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

abbrev SecE (U : UnifPre I D A G) {e : ℕ} (b : thickObj R I e G ⟶ thickObj R I e G) (n j : ℤ) : Type :=
  LB.Sec (LB.LinComb U.LG.L (K := Fin 2) ![(fstG I e G).left, b.left ≫ (fstG I e G).left] ![n, j])

def evalE (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {n j : ℤ} (τ : SecE U b n j)
    {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (J' : (Z ⟶ G.left) → U.LG.L.ι) : Z.presheaf.stalk z :=
  (DVR.wv U e x z (J (x ≫ (U.gt e).pG.left)) (J' (x ≫ (fstG I e G).left)) ^ n *
    DVR.wv U e (x ≫ b.left) z (J (x ≫ b.left ≫ (U.gt e).pG.left)) (J' (x ≫ b.left ≫ (fstG I e G).left)) ^ j).val *
    sval τ x z J'

def TExp (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {a : D.toPre.P.A ⟶ D.toPre.P.A}
    {n j : ℤ} (τ : SecE U b n j) {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) : Prop :=
  ∀ S : Finset Ix, (∀ i ∉ S, Van I (s i) e) → ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'),
    Good D.toPre.P.L z J → Good U.LG.L z J' → evalE U τ x z J J' =
      ∑ i ∈ S, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val

def zeroT (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) : SecT D a n j β := ⟨fun _ => 0, fun _ _ => by simp⟩

theorem sval_zeroT (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) {Z : Scheme.{0}} (x : Z ⟶ D.P.A.left) (z : Z) (J)
    (hJ : Good D.P.L z J) : sval (zeroT D a n j β) x z J = 0 := DVR.gs_zero x z _ (hJ.mem _ x)

namespace Witness


end Witness

end GlobalTheory.TwFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R]

def fnF (F : Type) [Field F] [Algebra (FractionRing R) F] (c : F) : Γ((TFK (R := R) F).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c

structure Eqv (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ)
    (lab : QkPt D F N → (TFK (R := R) F ⟶ A.A)) (E : Fam D F N → SecK A.L (snd (TFK (R := R) F) A.A).left N) : Prop where
  bij : Function.Bijective E
  add : ∀ s s' s'' : Fam D F N, (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) →
    ∀ j, (E s'').f j = (E s).f j + (E s').f j
  smul : ∀ (c : F) (s s' : Fam D F N), Fam.IsSmul D F c s s' → ∀ j, (E s').f j = liftFun A.A _ (fnF F c) * (E s).f j
  onto : ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x
  frame : ∀ p : QkPt D F N, ∃ w, GlobalTheory.UT.TXFrame N p w
  lift : ∀ p, ∃ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F), SymLift A.A A.L N N (lab p) θ
  act : ∀ (p : QkPt D F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D F N), GlobalTheory.UT.TXFrame N p w →
    SymLift A.A A.L N N (lab p) θ → PhiRel D F N p w s s' → IsActOf A.A A.L N θ (E s) (E s')

def LabExt {D : DegPre R} {A : PolAV (Sp (FractionRing R))} {F : Type} [Field F] [Algebra (FractionRing R) F] {N : ℕ}
    (em : Kb R →ₐ[FractionRing R] F) (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A))
    (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)) : Prop :=
  ∀ p p', QkExt em.toRingHom p p' → (lab' p').left = spMap em.toRingHom ≫ (lab p).left

def IntFam.Over {I : Ideal R} {D : DegPre R} {k : ℕ} (F₀ : IntFam I D k) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (s : Fam D F k) : Prop :=
  ∀ α : D.X, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (F₀.f α)
    (DegPre.prB D F).left 1

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

namespace GlobalTheory.LineForm

def hs (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ j ∈ Finset.range (m + 1), C ((-1) ^ j * ((m - j).choose j : ℝ)) * X 0 ^ (m - 2 * j) * X 1 ^ j

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def fld (w : A.Pt → Ev n) : A.Fld := fun x => w x

def evalF {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) : A.Fld :=
  fld A fun x => aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ))

def wInt [MeasurableSpace M] (g : M → ℝ) (α : A.Fld) : ℝ := ∫ y, g y ∂A.part α 1 - ∫ y, g y ∂A.part α (-1)

theorem wInt_one [MeasurableSpace M] (α : A.Fld) : wInt A (fun _ => 1) α = A.integral α := by
  simp [wInt, HolAtlas.integral]

end Manifold

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {D D' : ℕ}

variable (h : IsRegVar p D) (h' : IsRegVar p' D') (σ : k →+* ℂ)

end GlobalTheory.LineForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PullData
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolDeg GlobalTheory.TChart

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def CanonOn (Q : Data R) (W : (Sp R).Opens) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) : Prop :=
  P.IsLB ∧ ∃ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R))
    (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O)
    (inc : G ⟶ G') (pr : G' ⟶ G), (∀ y, PsiUnitOn D'.toPre y W) ∧ IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G ∧ pr ≫ inc = oG.act F.e ∧
      LBIso P ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)

variable {Q : Data R} {W W' : (Sp R).Opens} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {P : LB (G2 G).left}

theorem CanonOn.canon (h : CanonOn Q W G P) : Canon Q G P := by
  obtain ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, -, h⟩ := h
  exact ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, h⟩

section Pull

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def PullData (Q : Data R) (θ : R →+* V) (Q' : Data V) (e : Q'.X ≃+ Q.X) : Prop :=
  ∃ (β : Q'.B.left ⟶ Q.B.left) (β₂ : (G2 Q'.B).left ⟶ (G2 Q.B).left)
    (w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback Q'.B Q.B (spMap θ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (e a)).left) ∧
    ∀ a b, ∃ (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c (e a)) (Q.c (e b))) negε)) (x y : R) (k : (FractionRing R)ˣ)
      (k' : (FractionRing V)ˣ), u.IsGen ∧ θ y ≠ 0 ∧
      (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x ∧
      (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) ∧
      (∀ z J, Good Q.M.L z J → val (Q.tau (e a) (e b)) (𝟙 _) z J =
        gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) ∧
      ∀ z J J', Good Q.M.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' =
        gm (𝟙 (TK V).left) z ⊤ (unitOn k') *
          (lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' *
            val u ((TK V).hom ≫ spMap θ) z J)

end Pull

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

def symTup {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) : Fin N → R :=
  fun j => (Finset.univ.val.map c).esymm ((j : ℕ) + 1) ^ (N.factorial / ((j : ℕ) + 1))

def Prim {V K : Type} [CommRing V] [Field K] (i : V →+* K) {J : Type} (c : J → K) : Prop :=
  (∀ a, i.IsIntegralElem (c a)) ∧ ∃ a, c a ≠ 0 ∧ i.IsIntegralElem (c a)⁻¹

abbrev PCrd {o R : Type} [CommRing o] [CommRing R] {n : ℕ} (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) : Prop :=
  SecCoord (ProjSpace.O1 o n) (ProjSpace.coord o n) x v

section

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G)))

abbrev SecAt {R : Type} [CommRing R] (x : Sp R ⟶ S) : Type := LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))

def SecAt.pull {R K : Type} [CommRing R] [CommRing K] {x : Sp R ⟶ S} (θ : SecAt G L x) (i : R →+* K) :
    SecAt G L (spMap i ≫ x) :=
  VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) θ

def ThList (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) (θ : SecAt G L x) {N : ℕ} (pt : Fin N → (Over.mk x ⟶ G))
    (c : Fin N → K) : Prop :=
  Function.Injective pt ∧ (∀ a, ThG G L ρ m θ (pt a) (GlobalTheory.ZH.fn (c a))) ∧
    ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 →
      ∃ a, p.left = spMap i ≫ (pt a).left

def HasTh (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {N : ℕ} (c : Fin N → K) : Prop :=
  ∃ (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)), IsGenSec G L _ θ ∧ ThList G L ρ m x θ pt c

def HasTh₂ (m m' : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {N N' : ℕ} (c : Fin N → K) (c' : Fin N' → K) : Prop :=
  ∃ (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (pt' : Fin N' → (Over.mk x ⟶ G)),
    IsGenSec G L _ θ ∧ ThList G L ρ m x θ pt c ∧ ThList G L ρ m' x θ pt' c'

def SymAt (m : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) {N : ℕ} (e : Fin N → R) : Prop :=
  ∀ (K : Type) [Field K] (i : R →+* K) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K),
    ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ∀ j, i (e j) = symTup c j

def ThMap (m : ℕ) {o : Type} [CommRing o] {n : ℕ} {X : Scheme.{0}} (q : X ⟶ S) (f : X ⟶ PSpace o n) : Prop :=
  ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (c : Fin (n + 1) → K), HasTh G L ρ m (x ≫ q) c → PCrd (x ≫ f) (symTup c)

def PolFib (g : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S) : Prop :=
  ∃ (P : PolAV (Sp R)) (α : P.A.left ⟶ G.left), P.g = g ∧ IsGrpPullback P.A G x α ∧ LBIso P.L (L.pull α)

variable {G L ρ}

theorem hasTh_iff {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {N : ℕ} {c : Fin N → K} :
    HasTh G L ρ m x c ↔ HasTh₂ G L ρ m m x c c :=
  ⟨fun ⟨θ, pt, h, h'⟩ => ⟨θ, pt, pt, h, h', h'⟩, fun ⟨θ, pt, _, h, h', _⟩ => ⟨θ, pt, h, h'⟩⟩

end

end GlobalTheory.UMin
end
end

