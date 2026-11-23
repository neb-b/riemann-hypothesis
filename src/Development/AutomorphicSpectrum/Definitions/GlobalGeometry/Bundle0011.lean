module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BadExists
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOriginModel

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

variable {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (D.p + D.q)}

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y' : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y' Sys}

theorem pi_pt_ne (o : RootOrigin Y' S RM Fx) (x : o.Re.R.X) :
    ∃ a : ℂ, a ≠ 0 ∧ (fun i => o.Re.R.lift x x ⟨o.k₀, o.ix i⟩) = a • Fx.pt (o.Re.π x) := by
  obtain ⟨a, ha⟩ := o.π_pt x
  refine ⟨a, ?_, ha⟩
  rintro rfl
  obtain ⟨hnz, -⟩ := o.Re.R.mem x x (o.Re.R.mem_U x)
  obtain ⟨i, hi⟩ := hnz o.k₀
  apply hi
  have h := congrFun ha (o.ix.symm i)
  simp only [Equiv.apply_symm_apply, zero_smul, Pi.zero_apply] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.TowerOriginModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
section
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg)

noncomputable section

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
variable {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

structure IsPreFamily (x : (Σ k, J k) → Ω) (p : ℕ) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O)
    (φ : Equiv.Perm Sg) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) : Prop where
  famM : IsLatFamily O x fun c => (D c).M
  fam : ∀ τ, IsLatFamily O x (fun c => (D c).lie τ) ∧ IsLatFamily O x (fun c => (D c).W τ) ∧
    IsLatFamily O x (fun c => (D c).om τ) ∧ IsLatFamily O x (fun c => (D c).omHT τ) ∧
    IsLatFamily O x (fun c => (D c).Gam τ) ∧ IsLatFamily O x (fun c => (D c).Del τ) ∧
    IsLatFamily O x (fun c => (D c).Th τ)
  char : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O)
  base : ∀ c, mseg x c ≠ 0 → (D c).Base (chartRing O (mseg x) c) p (algebraMap O Ω w)
  test : ∀ c, mseg x c ≠ 0 → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C]
    (RC : Subalgebra O C), IsTestPt p (chartRing O (mseg x) c) RC → ∀ χ : Sg → F →*₀ C,
      (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
        χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →
      ((D c).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V]

def coordLat (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) : AddSubgroup (Fin m → Ω) :=
  ⨅ (q : Cpt ξ) (_ : InChart ξ (mseg y) c q) (_ : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q),
    (L q).toAddSubgroup.comap (Fintype.linearCombination Ω b).toAddMonoidHom

def IsFamilyOf (y : (Σ k, J k) → Ω) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) (L L' Lc Lc' : Sg → Lat ξ V)
    (b : ∀ τ, Fin (r τ) → V) (bc : ∀ τ, Fin (s τ) → V) : Prop :=
  ∀ c, mseg y c ≠ 0 → ∀ τ, (D c).lie τ = coordLat O y (L τ) (b τ) c ∧ (D c).W τ = coordLat O y (L' τ) (b τ) c ∧
    (D c).om τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc τ) (bc τ) c) ∧
    (D c).omHT τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc' τ) (bc τ) c)

namespace Fam


omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in
theorem mem_coordLat_iff (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) (a : Fin m → Ω) :
    a ∈ coordLat O y L b c ↔ ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) →
      ∑ i, a i • b i ∈ L q := by
  simp [coordLat, AddSubgroup.mem_iInf, Fintype.linearCombination_apply]



omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in
theorem chartRing_le_regAt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (q : Cpt ξ) (h1 : InChart ξ (mseg y) c q)
    (h2 : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) {a : Ω} (ha : a ∈ chartRing O (mseg y) c) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h1.2 j
  | algebraMap o => exact h2 o
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht





end Fam

end

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NotIsLineFnZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.FlatModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

variable {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ : FrameFn Xo c} {a : c.F}

theorem epsMul_zero_comp {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {v : epsAt x ⟶ G} (hv : IsTanAt G x v) : spMap (epsMul (0 : R)) ≫ v.left = (1 : epsAt x ⟶ G).left := by
  have h0 : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    ext z <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have h1 : spMap (epsMul (0 : R)) = spMap (algebraMap R (DualNumber R)) ≫
      spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    rw [h0, ← Spec.map_comp]; rfl
  rw [h1, Category.assoc]
  erw [hv]
  let k : epsAt x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
  have := congrArg (fun t => t.left) (MonObj.comp_one k (M := G))
  exact this

theorem isComb_one {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ}
    {v : Fin n → (epsAt x ⟶ G)} (hv : ∀ i, IsTanAt G x (v i)) (i : Fin n) :
    IsComb ((1 : Matrix (Fin n) (Fin n) R) i) v (v i) := by
  classical
  refine ⟨fun j => if i = j then v j else 1, fun j => ?_, ?_⟩
  · by_cases h : i = j
    · have h1 : epsMul (1 : R) = RingHom.id _ := by ext z <;> simp [epsMul]
      simp [h, Matrix.one_apply, h1, spMap]
    · simp only [h, Matrix.one_apply, if_false]
      exact (epsMul_zero_comp (hv j)).symm
  · induction n with
    | zero => exact i.elim0
    | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons]
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [List.prod_eq_one, (Fin.succ_ne_zero _).symm]
      · simp only [Fin.succ_ne_zero, if_false, _root_.one_mul, Fin.succ_inj]
        exact ih (v := fun j => v j.succ) (fun j => hv _) i


end GlobalTheory.CompanionTheory.Ar.Fl.FlatModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.ModelTest

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem bar_eq (H : Host E) (a : 𝓞 E) : RingOfIntegers.mapRingEquiv (cmConj E) a = H.bar a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq a]
  rfl

theorem overZp_of_inFibre {p : ℕ} (hp : p.Prime) (q : Cpt 𝔐.ξ) (hq : InFibre 𝔐.ξ p q) : OverZp 𝔐 p q := by
  intro r hr hrq
  by_contra hne
  have hloc : IsLocalRing (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) :=
    IsLocalRing.of_surjective' (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict
      (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict_surjective
  have key : ∀ m : ℕ, GlobalTheory.CompanionTheory.Ar.InFibre 𝔐.ξ m q → ¬ IsUnit ((m : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)) := by
    intro m hm hu
    apply hm
    obtain ⟨u, hu'⟩ := hu
    have h1 : (m : Ω) * (((u⁻¹ : (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)ˣ) : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) : Ω) = 1 := by
      have h2 := congrArg (fun x : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
      simpa [hu'] using h2
    have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨h0, natCast_mem _ m, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  have hcop : Nat.Coprime r p := (Nat.coprime_primes hr hp).2 hne
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q))
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
  · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
  · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)

variable {𝔐} {p : ℕ} {o : Type} [CommRing o] [Algebra o Ω]
  {Dc Dc' : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}

end GlobalTheory.CompanionTheory.Ar.HT.ModelTest
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def HodgeCpt.OmVB {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) : Prop :=
  ∀ p ∈ S, (𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).IsVBOn {q | InFibre 𝔐.ξ p q} (Module.finrank Ω 𝔐.Li) ⊤ ∧
    ∀ s, ((𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).map (𝔐.Vgen s).dualRestrict).IsVBOn {q | InFibre 𝔐.ξ p q}
      (labelRk D s) ⊤

def IsTowerOf (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (D.p + D.q)) : Prop :=
  ∃ o : TowerOrigin Y T, ∀ B a, (o.Or B a).𝔐.OmVB

def SplitComps {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) : Prop :=
  ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω), IsCptGen ξ →
    ξ ≫ Y.s = spMap (cst.comp β) → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ cst.range

end GlobalTheory.CompanionTheory.Ar
end
end

