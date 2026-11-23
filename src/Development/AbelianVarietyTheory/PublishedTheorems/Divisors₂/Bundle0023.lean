module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent unitOn)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta)
open ReciprocityTheory.ChartRestriction.G.Out (WeilIs)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R)

def IsConnecting (x : G.VecExt) (b : G.A 1) : Prop :=
  ∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
    G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b

variable {G}

end PDivGroup

namespace EpsWeil

variable {R : Type} [CommRing R] (D : Type) [CommRing D] [Algebra R D]


variable {D} in
def epsUnit (b : D) : (DualNumber D)ˣ where
  val := 1 + TrivSqZeroExt.inr b
  inv := 1 - TrivSqZeroExt.inr b
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp


variable (R) in
def epsMap : DualNumber R →ₐ[R] DualNumber D :=
  DualNumber.lift ⟨(Algebra.ofId R _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩

variable {D} {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def PairsTo (P : LB (A ⊗ B).left) (n : ℕ) (x : PDiv.SpAlg R D ⟶ A) (v : epsR R ⟶ B) (b : D) : Prop :=
  WeilIs (A ⊗ B) P (n : ℤ) (T := PDiv.SpAlg R (DualNumber D))
    (lift (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x) 1) (lift 1 (spOver (epsMap R D) ≫ v))
    (unitOn (epsUnit b))

theorem unitOn_bijective : Function.Bijective (unitOn (R := D)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of D)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem map_unitOn {D' : Type} [CommRing D'] (f : D →+* D') (u : Dˣ) :
    Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map f.toMonoidHom u) :=
  Units.ext (congrArg (fun q ↦ q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

end EpsWeil

namespace Published

namespace BarsottiTateDieudonne

def WittModule : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : PDivGroup p k → ModuleCat.{0} (WittVector p k))
      (map : ∀ G H : PDivGroup p k, (G ⟶ H) →+ (M H →ₗ[WittVector p k] M G))
      (red : ∀ G : PDivGroup p k,
        M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt),
      (∀ G : PDivGroup p k, Module.Free (WittVector p k) (M G) ∧ Module.Finite (WittVector p k) (M G) ∧
        Module.finrank (WittVector p k) (M G) = G.height ∧ Function.Surjective (red G) ∧
        (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧ map G G (𝟙 G) = LinearMap.id) ∧
      (∀ (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K),
        map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
      ∀ (G H : PDivGroup p k) (f : G ⟶ H) (m : M H),
        red G (map G H f m) = PDivGroup.rigExtMap f (red H m)

def WeilCompatible {p : ℕ} [Fact p.Prime] (e : DeRhamVectorExtension.Family p) (s : ℤˣ) : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : (p : R) = 0) ⦃A B : Over (Sp R)⦄ [GrpObj A] [GrpObj B] ⦃g : ℕ⦄
    (hA : IsAbelianScheme A), IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g B.hom → ∀ ⦃P : LB (A ⊗ B).left⦄, AbDual.IsDual A B P →
    ∀ ⦃φ : HdR A →ₗ[R] HdR B →ₗ[R] R⦄, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
    ∀ ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) ⦃h' : HdR B⦄ ⦃v : epsR R ⟶ B⦄, IsLieImage h' v →
    ∀ ⦃b : G.A 1⦄, EpsWeil.PairsTo P p (t.y 1) v b →
    ∀ ⦃c : primDR A⦄, (∀ h ∈ Fil A, φ h h' = h c) →
      G.IsConnecting (G.rigToExt (e (hR ▸ IsNilpotent.zero) hA t c)) (s • b)

def HodgeQuotient : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ (e : DeRhamVectorExtension.Family p) (s : ℤˣ),
    e.Natural ∧ e.Filtered ∧ e.Tangent ∧ WeilCompatible e s

end BarsottiTateDieudonne

def BarsottiTateDieudonne : Prop :=
  BarsottiTateDieudonne.WittModule ∧ BarsottiTateDieudonne.HodgeQuotient

namespace BarsottiTateDieudonne

end BarsottiTateDieudonne

end Published

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.H2EqZeroOfIsInitial
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbelianDualCrystal.Test

section Dual

variable {S : Scheme.{0}} {A B A₁ B₁ : Over S} [GrpObj A] [GrpObj B] [GrpObj A₁] [GrpObj B₁]
  {P : LB (A ⊗ B).left} {P₁ : LB (A₁ ⊗ B₁).left}

theorem point_ext (h : IsDual A B P) {T : Over S} {x y : T ⟶ B}
    (e : evc h.isLB (fst A T) (snd A T ≫ x) = evc h.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB h.isLB _
  refine (h.univ T _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ ?_)).unique
    ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.additive _ _ _ _

theorem dual_unique {B' : Over S} [GrpObj B'] {P' : LB (A ⊗ B').left} (h : IsDual A B P) (h' : IsDual A B' P') :
    Nonempty (B ≅ B') := by
  have key : ∀ {C D : Over S} [GrpObj C] [GrpObj D] {Q : LB (A ⊗ C).left} {Q' : LB (A ⊗ D).left}
      (q : IsDual A C Q) (q' : IsDual A D Q'), ∃ x : C ⟶ D, ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ C),
        evc q'.isLB a (b ≫ x) = evc q.isLB a b := by
    intro C D _ _ Q Q' q q'
    obtain ⟨x, hx, -⟩ := q'.univ C Q q.isLB q.additive
    refine ⟨x, fun Y a b ↦ ?_⟩
    have := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff q.isLB (pull_isLB q'.isLB _)).2 hx)
    rw [cls_ev q'.isLB, pull_evc] at this
    simpa [evc] using this.symm
  obtain ⟨x, hx⟩ := key h h'
  obtain ⟨y, hy⟩ := key h' h
  exact ⟨⟨x, y, point_ext h (by rw [← Category.assoc, hy, hx, Category.comp_id]),
    point_ext h' (by rw [← Category.assoc, hx, hy, Category.comp_id])⟩⟩

end Dual

section Crystal

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I} {π : R →+* R₀}

end Crystal

end GlobalTheory.Published.AbelianDualCrystal.Test
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def IsFineModuli {B : Type} [CommRing B] {M : Scheme.{0}} (s : M ⟶ Sp B) {N : ℕ} {U : Obj F 𝔠 M}
    (α : U.Level N) : Prop :=
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp B) (X : Obj F 𝔠 S) (β : X.Level N),
    ∃! b : S ⟶ M, b ≫ s = t ∧ Obj.IsLevelPull β α b

def IsRelCI {B : Type} [CommRing B] {M : Scheme.{0}} (s : M ⟶ Sp B) (n : ℕ) : Prop :=
  (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp B), topologicalKrullDim ↥(pullback s t) = n) ∧
    ∀ x : M, ∃ (V : M.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (c : ℕ) (g : Fin c → MvPolynomial (Fin (c + n)) B)
      (e : Γ(M, V) ≃+* MvPolynomial (Fin (c + n)) B ⧸ Ideal.span (Set.range g)),
      ∀ b : B, e (constFn s V b) = Ideal.Quotient.mk _ (MvPolynomial.C b)

def Obj.IsLinearKS {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (κ : Fil X.A →ₗ[R] X.Lie) : Prop :=
  ∀ (a : 𝓞 F) (x y : Fil X.A), (y : HdR X.A) = act (dp0 R) (𝟙 _) X.rm a x → κ y = a • κ x

def Obj.HasKS {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp (DualNumber R))}
    {i : X.A.left ⟶ X'.A.left} (h : X.IsPullBy X' (DeRham.epsRed R) i) (κ : Fil X.A →ₗ[R] X.Lie) : Prop :=
  ∀ x : Fil X.A, IsKSValue h.grp (x : HdR X.A) (κ x).hom

end GlobalTheory.RealMult

namespace GlobalTheory.Published

def DelignePappasModel : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 3 ≤ N →
    ∃ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N),
      IsFineModuli s α ∧ IsSeparated s ∧ QuasiCompact s ∧ LocallyOfFinitePresentation s ∧
      Flat s ∧ IsRelCI s (Module.finrank ℚ F) ∧
      (∃ V : M.Opens, (V : Set M) = U.rapLocus ∧ SmoothOfRelativeDimension (Module.finrank ℚ F) (V.ι ≫ s) ∧
        M.basicOpen ((discr F : ℤ) : Γ(M, ⊤)) ≤ V ∧
        ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
          pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) ∧
      (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) ∧
      ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra (Localization.Away (N : ℤ)) B]
        [IsCyclotomicExtension {N} (Localization.Away (N : ℤ)) B]
        (x : ↥(pullback s (spMap (algebraMap (Localization.Away (N : ℤ)) B))))
        (K : Type) [Field K] (t : Sp K ⟶ Sp B),
        IsIrreducible (pullback.fst (pullback.snd s (spMap (algebraMap (Localization.Away (N : ℤ)) B))) t ⁻¹'
          connectedComponent x)

def HilbertQExpansion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (𝔞 𝔟 : FracId F) (k : ℕ) (R₀ : Subring ℂ)
      (g : ((F →+* ℝ) → ℂ) → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      IsHolForm 𝔞 𝔟 k g → HasFourier 𝔞 𝔟 g a → (∀ ξ, a ξ ∈ R₀) →
      ∃! r : Rule (rapObj (𝔞 * 𝔟⁻¹)) R₀ k, r.HasValues e 𝔞 𝔟 g

def GoetzkyKoecher : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (𝔞 𝔟 : FracId F) (k : ℕ) (g : ((F →+* ℝ) → ℂ) → ℂ), IsHolForm 𝔞 𝔟 k g →
      (∃! a, HasFourier 𝔞 𝔟 g a) ∧
      ∀ a, HasFourier 𝔞 𝔟 g a → ∀ ξ, a ξ ≠ 0 → ξ = 0 ∨ IsTotPos (ξ : F)

def HilbertKodairaSpencer : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)), X.IsRapoport →
    (∀ (X' : Obj F 𝔠 (Sp (DualNumber R))) (i : X.A.left ⟶ X'.A.left) (h : X.IsPullBy X' (DeRham.epsRed R) i),
      ∃! κ, X.IsLinearKS κ ∧ Obj.HasKS h κ) ∧
    (∀ κ, X.IsLinearKS κ → ∃ (X' : Obj F 𝔠 (Sp (DualNumber R))) (i : X.A.left ⟶ X'.A.left)
      (h : X.IsPullBy X' (DeRham.epsRed R) i), Obj.HasKS h κ) ∧
    ∀ (X' X'' : Obj F 𝔠 (Sp (DualNumber R))) (i' : X.A.left ⟶ X'.A.left) (i'' : X.A.left ⟶ X''.A.left)
      (h' : X.IsPullBy X' (DeRham.epsRed R) i') (h'' : X.IsPullBy X'' (DeRham.epsRed R) i'') κ, Obj.HasKS h' κ → Obj.HasKS h'' κ →
      ∃ ψ : X'.A.left ⟶ X''.A.left, X'.IsPullBy X'' (𝟙 _) ψ ∧ i' ≫ ψ = i''

def RealMultDeRhamRank : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsLocalRing R]
    (X : Obj F 𝔠 (Sp R)),
    letI := tensorModule (dp0 R) (𝟙 _) X.rm
    Nonempty (Module.Basis (Fin 2) (R ⊗[ℤ] 𝓞 F) (HdR X.A))

def HilbertBlumenthal : Prop :=
  DelignePappasModel ∧ HilbertQExpansion ∧ GoetzkyKoecher ∧ HilbertKodairaSpencer ∧ RealMultDeRhamRank

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsPerfectOfIsDual
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.PoincareDeRhamDuality.Test

theorem isPerfect_of_isDual (D : DualAbelianScheme) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (h : IsDual A B P) : IsPerfect A B P := by
  obtain ⟨B', _, P', -, -, h₁, h₂⟩ := D S A hA
  obtain ⟨u, hu, -⟩ := h.univ B' P' h₁.isLB h₁.additive
  refine ⟨h.isLB, (triv_ev_iff h.isLB _ _).2 (h.additive.evc_one h.isLB _), h.zero, fun T x hx ↦ ?_,
    fun _ ↦ h.eq_one⟩
  apply (h₁.isPerfect h₂).ker_left T x
  apply (triv_ev_iff h₁.isLB _ _).2
  have e := congrArg (CechPic.pull (lift (fst T B') (snd T B' ≫ u)).left) ((triv_ev_iff h.isLB _ _).1 hx)
  rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
  have k := (cls_eq_iff h₁.isLB (pull_isLB h.isLB _)).2 hu
  rw [evc, k, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc, e]

variable (R : Type) [CommRing R]

end GlobalTheory.Published.PoincareDeRhamDuality.Test
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Published

def SiegelToroidalPolCharts : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n →
    ∃ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (_ : IsOpenImmersion j)
      (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ),
      IsProjOver s ∧ SmoothOfRelativeDimension (g * (g + 1) / 2) s ∧ j ≫ s = F.s ∧
      (∀ x : S, x ∈ closure (Set.range j ∩ s ⁻¹' {s x})) ∧
      IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j ∧
      1 ≤ d ∧ (∀ x : S, GlobalTheory.PolDeg.HasPolChart F s j e φ BD d x) ∧
      1 ≤ N ∧ IsGenerated (lbPow (hodge G g) N) ∧
      ∃ k : ℕ, IsAmpleLB (CechPic.tens (lbPow (hodge G g) (N * k)) (CechPic.dual BD.lb))

end GlobalTheory.Published
end
end

