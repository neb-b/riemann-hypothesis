module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex
section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

def vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : F :=
  valF r (LB.wchart L φ fun k => J (r ≫ φ k)) (t.s fun k => J (r ≫ φ k)).val

def sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : F :=
  valF r (LB.wchart L φ fun k => J (r ≫ φ k)) (s.f fun k => J (r ≫ φ k))
end Val

abbrev fnOf {F : Type} [Field F] (x : F) : Γ(Sp F, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x
section Num
variable {R : Type} [CommRing R] [IsDomain R]

structure NumOf (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) where

  J : (Sp F ⟶ D.P.A.left) → D.P.L.ι

  good : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)

  th : H0 D.P.L 1

  th_gen : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j

  eA : N.A ≃* (TF (R := R) F ⟶ D.P.A)

  eX : N.X ≃+ D.X

  c_eq : ∀ χ, eA (N.c χ) = DegPre.cF D F (eX χ)

  θ_eq : ∀ x y u, (N.θ x y u : F) = vF (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
    (lift (eA x) (lift (eA y) (eA u))).left J

  σ_eq : ∀ x, (N.σ x : F) = vF D.sym (eA x).left J

  th_eq : ∀ x, N.th x * vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom J =
    sF th (eA x).left J

  ψ_eq : ∀ χ, (N.ψ χ : F) = vF (D.psi (eX χ)) (jFK (R := R) F) J *
    vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom J
variable {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {N : NumD F}

def NumOf.Pt (ν : NumOf D F N) (g : GtPtF D F) (gv : N.Gt) : Prop :=
  ν.eA gv.b = g.b ∧ ∀ χ, (gv.s χ : F) = vF (g.s (ν.eX χ)) (𝟙 (Sp F)) ν.J

def NumOf.QPt (ν : NumOf D F N) {k : ℕ} (p : QkPt D F k) (q : N.QT k) : Prop :=
  ν.eX q.1.1.toAdd = p.y ∧ ν.Pt p.g q.1.2

def NumOf.Integral (ν : NumOf D F N) (S : ValuationSubring F) : Prop :=
  ∀ x : TF (R := R) F ⟶ D.P.A, ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U (ν.J x.left)
end Num

def NumOf.IntN {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [NormedField C] [Algebra (FractionRing R) C]
    {N : NumD C} (ν : NumOf D C N) : Prop :=
  ∃ S : ValuationSubring C, (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ ν.Integral S

def CExt (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (C : Type) [NormedField C] [Algebra (FractionRing R) C] : Prop :=
  (∀ r : R, ‖algebraMap (FractionRing R) C (algebraMap R _ r)‖ ≤ 1) ∧
    ∀ r ∈ I, ‖algebraMap (FractionRing R) C (algebraMap R _ r)‖ < 1

def IsCoordPt {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A)) (z : T ⟶ P.A)
    (v : I → Γ(T.left, ⊤)) : Prop :=
  Odd k ∧ IsUnit (k : Γ(T.left, ⊤)) ∧
  ∃ (th : LB.Sec (LPow P.A P.L 1 T)) (s1 : LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]))
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => (k : ℤ) ^ 2)))
    (U : I → ThetaGrp P.A P.L ((k : ℤ) ^ 2) T) (s2 : I → LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T)),
    IsGenSec P.A P.L 1 th ∧ α.IsGen ∧ τ.IsGen ∧
    IsTwistPull P.A P.L (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α th s1 ∧
    (∀ i, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) (U i)) ∧
    (∀ i, IsActOf P.A P.L ((k : ℤ) ^ 2) (U i) s1 (s2 i)) ∧
    ∀ i, IsValueAt P.A P.L ((k : ℤ) ^ 2) (s2 i) z τ (v i)

def TwRel {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (u r : Oˣ) {j : ℕ} (p : N.QT j)
    (p' : (N.twist β u).QT j) : Prop :=
  p'.1.1 = p.1.1 ∧ p'.1.2.b = p.1.2.b ∧ ∀ z : N.X, p'.1.2.s z = p.1.2.s z * r ^ β.be p.1.1.toAdd z
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure Full (D : Datum H) (K : Type) [Field K] where

  P : PolAV (Sp K)

  oa : letI := H.starRing; P.OAct (𝓞 E)

  prim : letI := H.starRing; LBIso P.L (cubeLB P.A ![𝟙 P.A, oa.act H.w0] P.L)

  ρ : K

  ρ_sq : ρ ^ 2 = -(H.d : K)

  det : letI := H.starRing; DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp K)) ρ

  I : letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ P.A) (fun a g => g ≫ oa.act a)
    (fun n g g' c => WeilIs P.A P.L n g g' (unitOn c))

  closed : IsAlgClosed K

def Full.Theta {D : Datum H} {K : Type} [Field K] (o : Full D K) (m : ℕ) (v : D.La → K) : Prop :=
  IsThetaPt o.P m (T := baseOver (Sp K)) (o.I.ev (m ^ 2)) fun a => fnOf (v a)

def Full.Coord {D : Datum H} {K : Type} [Field K] (o : Full D K) (m : ℕ) (z : baseOver (Sp K) ⟶ o.P.A) (v : D.La → K) : Prop :=
  IsCoordPt o.P m (T := baseOver (Sp K)) (o.I.ev (m ^ 2)) z fun a => fnOf (v a)

abbrev cf {K : Type} [CommRing K] (ζ ρ : K) : MvPolynomial (Fin 2) ℤ →+* K := MvPolynomial.eval₂Hom (Int.castRingHom K) ![ζ, ρ]

def Compat (H : Host E) (n : ℕ) {K : Type} [CommRing K] (ζ ρ : K) : Prop := ∀ c, cf (zeta n) H.rt0 c = 0 → cf ζ ρ c = 0

def VanishC (D : Datum H) (m : ℕ) (G : MvPolynomial D.La (MvPolynomial (Fin 2) ℤ)) : Prop :=
  Odd m ∧ (∃ d, G.IsHomogeneous d) ∧ ∀ o : Full D ℂ, o.ρ = H.rt0 → (o.I.ζ (m ^ 2) : ℂ) = zeta (m ^ 2) →
    ∀ v, o.Theta m v → MvPolynomial.eval₂ (cf (zeta (m ^ 2)) H.rt0) v G = 0

structure ArcF (D : Datum H) (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] where

  D₀ : DegPre R

  [mod : Module (𝓞 E) D₀.X]

  oa : letI := H.starRing; D₀.OAct (𝓞 E)

  even : D₀.PsiEven

  bimult : D₀.TauBimult

  w0 : letI := H.starRing; TraceFormTwistIso D₀ oa H.w0

  ρ : F

  ρ_sq : ρ ^ 2 = -(H.d : F)

  det : letI := H.starRing; ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct oa.onB.toRingAct)
    (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧
    n + Module.finrank (𝓞 E) D₀.X = open Classical in if τ H.rt = ρ then D.p else D.q

  I : TateIsoQ D D₀ oa F

  N : NumD F

  ν : NumOf D₀ F N

  q : ∀ n : ℕ, D.La → N.QT n

  hq : ∀ n a, ν.QPt (I.ev n a) (q n a)

  closed : IsAlgClosed F
attribute [instance] ArcF.mod
namespace ArcF
variable {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] (A : ArcF D R F)

def act (a : 𝓞 E) (y : A.N.X) : A.N.X := A.ν.eX.symm (a • A.ν.eX y)

def Bal {k : ℕ} (β : A.N.Form k) : Prop := ∀ a y z, β.be (A.act a y) z = β.be y (A.act (H.bar a) z)

def Over {R' : Type} [CommRing R'] [IsDomain R'] {F' : Type} [Field F'] [Algebra (FractionRing R') F'] (f : F →+* F')
    (A' : ArcF D R' F') : Prop :=
  ∃ I : NumD.Hom f A.N A'.N, f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧
    (∀ a y, I.e (A.act a y) = A'.act a (I.e y)) ∧
    ∀ n a, 0 < n → ∃ p' : A'.N.QT n, p'.1.1.toAdd = I.e (A.q n a).1.1.toAdd ∧ I.Rel (A.q n a).1.2 p'.1.2 ∧ A'.N.QEq p' (A'.q n a)
end ArcF

def Roots {C : Type} [Field C] (u : Cˣ) (r : ℕ → Cˣ) : Prop := r 1 = u ∧ ∀ n m, 0 < n → 0 < m → r (n * m) ^ m = r n

def Realises {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {C : Type} [NormedField C] [Algebra (FractionRing R) C]
    (o : Full D C) (A : ArcF D R C) {k : ℕ} (β : A.N.Form k) (u : Cˣ) (r : ℕ → Cˣ) : Prop :=
  Roots u r ∧ o.ρ = A.ρ ∧ (∀ n, 0 < n → o.I.ζ n = A.I.ζ n) ∧
    ∀ m, Odd m → ∀ p : D.La → (A.N.twist β u).QT (m ^ 2), (∀ a, TwRel β u (r (m ^ 2)) (A.q _ a) (p a)) →
      (∀ a, Summable ((A.N.twist β u).txT m (p a))) ∧ o.Theta m (fun a => (A.N.twist β u).tx m (p a)) ∧
      ∀ j, 0 < j → ∀ b (q : (A.N.twist β u).QT j), TwRel β u (r j) (A.q j b) q →
        (∀ a, Summable ((A.N.twist β u).evT m (p a) q.1.2)) ∧
        o.Coord m (o.I.ev j b) fun a => (A.N.twist β u).ev m (p a) q.1.2

abbrev CDV (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] : Prop := GlobalTheory.LN.CDvr W

theorem NumOf.pt_unique {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {g : GtPtF D F} {v v' : N.Gt} (h : ν.Pt g v) (h' : ν.Pt g v') : v = v' :=
  NumD.Gt.ext (ν.eA.injective (h.1.trans h'.1.symm)) (funext fun χ => Units.ext ((h.2 χ).trans (h'.2 χ).symm))

theorem Roots.pow {C : Type} [Field C] {u : Cˣ} {r : ℕ → Cˣ} (h : Roots u r) {j : ℕ} (hj : 0 < j) : r j ^ j = u := by
  have := h.2 1 j one_pos hj
  rwa [_root_.one_mul, h.1] at this

theorem existsUnique_twRel {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (u r : Oˣ) {j : ℕ} (h : r ^ j = u)
    (p : N.QT j) : ∃! p' : (N.twist β u).QT j, TwRel β u r p p' := by
  have hp : p.1.2 ^ j = N.io p.1.1.toAdd := p.2
  have h' := N.twG_pow β r p.1.2 (fun z => β.be p.1.1.toAdd z) (fun _ _ => map_add _ _ _) j
  let G : (N.twist β r).Gt := N.twG β r p.1.2 (fun z => β.be p.1.1.toAdd z) (fun _ _ => map_add _ _ _)
  let g : (N.twist β u).Gt := ⟨G.b, G.s, G.mult⟩
  have e : ∀ n : ℕ, (g ^ n).b = (G ^ n).b ∧ (g ^ n).s = (G ^ n).s := fun n => by
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      rw [pow_succ, pow_succ]
      refine ⟨congrArg (· * G.b) ih.1, funext fun z => ?_⟩
      change (g ^ n).s z * G.s z / N.θ (N.c z) (g ^ n).b G.b = (G ^ n).s z * G.s z / N.θ (N.c z) (G ^ n).b G.b
      rw [ih.1, ih.2]
  refine ⟨⟨(p.1.1, g), ?_⟩, ⟨rfl, rfl, fun _ => rfl⟩, fun q hq => Subtype.ext (Prod.ext hq.1
    (NumD.Gt.ext hq.2.1 (funext hq.2.2)))⟩
  refine NumD.Gt.ext ((e j).1.trans (h'.1.trans (by rw [hp]; rfl))) ((e j).2.trans (funext fun (z : N.X) =>
    (h'.2 z).trans ?_))
  rw [hp, mul_comm (β.be _ _), zpow_mul, zpow_natCast, h]
  exact (N.twist_τ β u _ z).symm


open ReciprocityTheory.ChartRestriction.G.Out.InhTate GlobalTheory.ToricData in
theorem isCoordPt_one_iff {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v : I → Γ(T.left, ⊤)) :
    IsCoordPt P k x 1 v ↔ Odd k ∧ IsUnit (k : Γ(T.left, ⊤)) ∧ IsThetaPtOver P k x v := by
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨th, s1, α, τ, U, s2, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨th, s1, α, τ, U, s2, v, 1, h1, h2, h3, h4, h5, h6, h7, fun i => (_root_.one_mul _).symm⟩
  · rintro ⟨th, s1, α, τ, U, s2, w, u, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨th, s1, α, ⟨fun j => τ.s j * gv u⁻¹ _⟩, U, s2, h1, h2, fun i j => ?_, h4, h5, h6, fun i j => ?_⟩
    · rw [map_mul, map_mul, h3 i j, res_gv, res_gv, _root_.mul_assoc]
    · rw [h7 i j, h8 i, map_mul]
      have e : (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j ≤ ⊤)).op).hom u.val *
          (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j ≤ ⊤)).op).hom
            (u⁻¹).val = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      have key : ∀ {A : Type} [CommRing A] (a b c d : A), a * b = 1 → c * d = a * c * (d * b) := fun a b c d h => by
        linear_combination (-(c * d)) * h
      exact key _ _ _ _ e

theorem charZero_of_isPrimitiveRoot {K : Type} [Field K] {ζ : ℕ → Kˣ} (h : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) :
    CharZero K :=
  charZero_of_inj_zero fun n hn => by
    by_contra h0
    haveI : NeZero n := ⟨h0⟩
    exact (IsPrimitiveRoot.coe_units_iff.2 (h n (Nat.pos_of_ne_zero h0))).neZero'.out hn

theorem Full.charZero {D : Datum H} {K : Type} [Field K] (o : Full D K) : CharZero K :=
  charZero_of_isPrimitiveRoot o.I.ζ_prim

theorem ArcF.charZero {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (A : ArcF D R F) : CharZero F :=
  charZero_of_isPrimitiveRoot A.I.ζ_prim

theorem isUnit_natCast_sp {K : Type} [Field K] {m : ℕ} (hm : (m : K) ≠ 0) :
    IsUnit (m : Γ((baseOver (Sp K)).left, ⊤)) := by
  have := (IsUnit.mk0 (m : K) hm).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  rwa [map_natCast] at this

namespace ValInh
open ReciprocityTheory.ChartRestriction.G.Out.InhTate GlobalTheory.ToricData

section Toric
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (q : X → (FractionRing K)ˣ) (he : ∀ y, q (-y) = q y) (hb : ∀ a a' b, polar q (a + a') b = polar q a b * polar q a' b)
  (F : Type) [Field F] [Algebra (FractionRing K) F]

def toricNum : NumD F where
  toNumB := NumB.triv PUnit fun _ => 1
  X := X
  c _ := 1
  c_add _ _ := rfl
  ψ y := Units.map (algebraMap (FractionRing K) F).toMonoidHom (q y)
  even y := by
    change _ * 1 = _
    rw [he, _root_.mul_one]
  bimult a a' b := by
    change _ * 1 = _
    have := congrArg (Units.map (algebraMap (FractionRing K) F).toMonoidHom) (hb a a' b)
    simpa only [polar, map_mul, map_inv, _root_.mul_one, div_eq_mul_inv] using this

end Toric

section ThetaShiftProofs
open GlobalTheory.HostModel GlobalTheory.HostModel.ConjDual
variable (H : Host E) (K : Type) [CommRing K] [IsDomain K]
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing K) F] (ρ : F) (hρ : ρ ^ 2 = -(H.d : F)) (ζ : ℕ → Fˣ)
  (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)

end ThetaShiftProofs

theorem lbIso_of_g_one {X : Scheme.{0}} {L M : LB X} (hL : ∀ i j, L.g i j = 1) (hM : ∀ i j, M.g i j = 1) : LBIso L M := by
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have e : (LB.div M L).g i j = 1 := by simp only [LB.div, hL, hM, map_one, inv_one, _root_.mul_one]; rfl
  rw [e, map_one, map_one, _root_.mul_one]

section RankZero
open GlobalTheory.HostModel
variable (H : Host E) (K : Type) [CommRing K] [IsDomain K] [Algebra (FractionRing K) ℂ]

end RankZero

end ValInh
end GlobalTheory.Ex
end
