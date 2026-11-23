module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDvrModelLatticeValuation
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

def tr {A B : Subring Ω} (h : A = B) (N : Submodule B Ω) : Submodule A Ω where
  carrier := N
  add_mem' := N.add_mem
  zero_mem' := N.zero_mem
  smul_mem' := fun c _ hx => N.smul_mem ⟨c.1, h ▸ c.2⟩ hx

theorem tr_eq_span_iff {A B : Subring Ω} (h : A = B) (N : Submodule B Ω) (S : Set Ω) :
    tr h N = Submodule.span A S ↔ N = Submodule.span B S := by
  subst h
  have : tr rfl N = N := by ext; rfl
  rw [this]

theorem genMap_stalkMap₀ (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

def push (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (p : Cpt ξ') : Cpt (ξ' ≫ g) :=
  ⟨g p.1, p.2.map g.continuous⟩

variable {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {g : X' ⟶ X}

def pullL (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) (L : Lat (ξ' ≫ g) Ω) : Lat ξ' Ω :=
  fun p => tr (hr p) (L (push ξ' g p))

section

variable (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) {L : Lat (ξ' ≫ g) Ω}
include hr

theorem unit_iff (p : Cpt ξ') (a : Ω) : unitAt ξ' p a ↔ unitAt (ξ' ≫ g) (push ξ' g p) a := by
  unfold unitAt
  rw [hr p]

theorem pull_span_iff (p : Cpt ξ') (S : Set Ω) :
    pullL hr L p = Submodule.span (regAt ξ' p) S ↔
      L (push ξ' g p) = Submodule.span (regAt (ξ' ≫ g) (push ξ' g p)) S :=
  tr_eq_span_iff _ _ _

theorem isVB_pull (hL : L.IsVB 1 ⊤) : (pullL hr L).IsVB 1 ⊤ := by
  intro p _
  obtain ⟨U, hU, b, hb, h⟩ := hL (push ξ' g p) trivial
  refine ⟨g ⁻¹ᵁ U, hU, b, hb, fun q _ hq => ?_⟩
  obtain ⟨h1, h2⟩ := h (push ξ' g q) trivial hq
  exact ⟨h1, (pull_span_iff hr q _).2 h2⟩

omit hr in
theorem isIntegral_congr {A B : Subring Ω} (h : A = B) {a : Ω} (ha : IsIntegral A a) : IsIntegral B a := by
  subst h
  exact ha

theorem normal_pull (hN : NormalCpt (ξ' ≫ g)) : NormalCpt ξ' := fun p a ha => by
  rw [hr p]
  exact hN _ a (isIntegral_congr (hr p) ha)

theorem isGenAt_pull {p : Cpt ξ'} {t : Ω} (h : L.IsGenAt (push ξ' g p) t) : (pullL hr L).IsGenAt p t :=
  ⟨h.1, (pull_span_iff hr p _).2 h.2⟩

theorem order_back {σ ϖ : Ω} {M : ℕ} {a : ℤ} {p : Cpt ξ'} (h : OrderAt (pullL hr L) σ ϖ M a p) :
    OrderAt L σ ϖ M a (push ξ' g p) := by
  obtain ⟨e, c, he, h1, h2, h3⟩ := h
  exact ⟨e, c, he, (pull_span_iff hr p _).1 h1, h2, (unit_iff hr p _).1 h3⟩

theorem trivMod_pull {ϖ l u : Ω} (e : l = ϖ * u) (hϖ : ∀ p, ϖ ∈ regAt ξ' p) (hu : ∀ p, u ∈ regAt ξ' p)
    (hT : TrivMod L l) : TrivMod (pullL hr L) ϖ := by
  obtain ⟨t, ht⟩ := hT
  have key : ∀ p, ¬ unitAt ξ' p ϖ → ¬ unitAt (ξ' ≫ g) (push ξ' g p) l := fun p hp hl =>
    hp (ZUnit.of_mul (hϖ p) (hu p) ((unit_iff hr p _).2 (e ▸ hl)))
  refine ⟨fun p => t (push ξ' g p), fun p hp => ?_⟩
  obtain ⟨U, hU, H⟩ := ht _ (key p hp)
  refine ⟨g ⁻¹ᵁ U, hU, fun q hq hq' => ?_⟩
  obtain ⟨h0, h1, y, hy, hty⟩ := H (push ξ' g q) hq (key q hq')
  refine ⟨h0, (pull_span_iff hr q _).2 h1, u • y, ?_, ?_⟩
  · exact (L (push ξ' g q)).smul_mem ⟨u, hr q ▸ hu q⟩ hy
  · change t (push ξ' g p) - t (push ξ' g q) = ϖ • u • y
    rw [hty, e, mul_smul]

end

theorem valAt_zero_down {R : Type} [CommRing R] [IsLocalRing R] (hc : IsCptGen ξ')
    (z : Spec (CommRingCat.of R) ⟶ X') {ϖ u l : Ω} (e : l = ϖ * u) (h : genPt ξ' ⤳ centre z)
    (hv : ValAt ξ' z ϖ 0) (hu : u ∈ regAt ξ' ⟨centre z, h⟩)
    (hl : l ∈ regAt (ξ' ≫ g) (push ξ' g ⟨centre z, h⟩)) : ValAt (ξ' ≫ g) (z ≫ g) l 0 := by
  obtain ⟨h', s, hs, h0⟩ := hv
  obtain ⟨t, ht⟩ : ∃ t : X'.presheaf.stalk (centre z), genMap ξ' ⟨centre z, h⟩ t = u := hu
  obtain ⟨w, hw⟩ := hl
  have e1 : (g.stalkMap (centre z)).hom w = s * t := by
    apply hc.inj ⟨centre z, h⟩
    rw [genMap_stalkMap₀ ξ' g ⟨centre z, h⟩ (push ξ' g ⟨centre z, h⟩).2 w, map_mul, ht]
    refine hw.trans ?_
    rw [e, ← hs]
  have e2 : (Scheme.stalkClosedPointTo (z ≫ g)).hom w =
      (Scheme.stalkClosedPointTo z).hom ((g.stalkMap (centre z)).hom w) :=
    congrArg (fun t => t.hom w) (Scheme.stalkClosedPointTo_comp z g)
  refine ⟨(push ξ' g ⟨centre z, h⟩).2, w, hw, e2.trans ?_⟩
  rw [e1]
  exact (map_mul (Scheme.stalkClosedPointTo z).hom s t).trans
    ((congrArg (fun x : R => x * (Scheme.stalkClosedPointTo z).hom t) h0).trans (zero_mul _))

theorem valAt_up {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X')
    (h : genPt ξ' ⤳ centre z) {a : Ω} {r : R} (hv : ValAt (ξ' ≫ g) (z ≫ g) a r) : ValAt ξ' z a r := by
  obtain ⟨h', s, hs, rfl⟩ := hv
  exact ⟨h, (g.stalkMap (centre z)).hom s, (genMap_stalkMap₀ ξ' g ⟨centre z, h⟩ h' s).trans hs,
    (congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z g)).symm⟩

def curvePush {ϖ l : Ω} (Γ : FibreCurve ξ' ϖ) (hz : ValAt (ξ' ≫ g) (Γ.η ≫ g) l 0) : FibreCurve (ξ' ≫ g) l where
  k := Γ.k
  κ := Γ.κ
  fg := Γ.fg
  trdeg := Γ.trdeg
  C := Γ.C
  w_pos := Γ.w_pos
  triv := Γ.triv
  all := Γ.all
  η := Γ.η ≫ g
  η_spec := hz.1
  η_zero := hz
  z := fun i => Γ.z i ≫ g
  z_gen := fun i => by rw [← Category.assoc, Γ.z_gen]

theorem hasDeg_back (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) {L : Lat (ξ' ≫ g) Ω} {ϖ l : Ω}
    (Γ : FibreCurve ξ' ϖ) (hz : ValAt (ξ' ≫ g) (Γ.η ≫ g) l 0) (h : (curvePush Γ hz).HasDeg L 0) :
    Γ.HasDeg (pullL hr L) 0 := by
  obtain ⟨e, f, r, he, hf, hv, hfin, hd⟩ := h
  refine ⟨e, f, r, isGenAt_pull hr he, fun i => ⟨Γ.z_spec i, ?_⟩, fun i => ⟨(hv i).1, ?_⟩, hfin, hd⟩
  · obtain ⟨_, h2⟩ := hf i
    exact isGenAt_pull hr h2
  · exact valAt_up _ Γ.η_spec (hv i).2

theorem numTrivMod_pull (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) (hc : IsCptGen ξ')
    {L : Lat (ξ' ≫ g) Ω} {ϖ l u : Ω} (e : l = ϖ * u) (hϖ : ∀ p, ϖ ∈ regAt ξ' p) (hu : ∀ p, u ∈ regAt ξ' p)
    (hT : NumTrivMod L l) : NumTrivMod (pullL hr L) ϖ := fun Γ => by
  let p : Cpt ξ' := ⟨centre Γ.η, Γ.η_spec⟩
  have hl : l ∈ regAt (ξ' ≫ g) (push ξ' g p) := by
    have h1 := mul_mem (hϖ p) (hu p)
    rwa [← e, hr p] at h1
  have hz := valAt_zero_down (g := g) hc Γ.η e Γ.η_spec Γ.η_zero (hu p) hl
  exact hasDeg_back hr Γ hz (hT (curvePush Γ hz))

theorem order_at_place : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X' ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O) (L : Lat ξ Ω) (σ : Ω) (ℓ : ℕ) (u : O), PropZ → Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ξ' ≫ g = ξ → IsCptGen ξ → IsCptGen ξ' → (∀ q' : X', genPt ξ' ⤳ q') → NormalCpt ξ → ConstClosed O Ω → (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) → L.IsVB 1 ⊤ → (∀ p ∈ genFibre ℤ ξ, L.IsGenAt p σ) → (ℓ : Ω) = algebraMap O Ω (ϖ * u) → (TrivMod L (ℓ : Ω) ∨ NumTrivMod L (ℓ : Ω)) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, (∃ p' : Cpt ξ', g p'.1 = p.1) → OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  intro X X' Ω _ _ ξ ξ' g O _ _ _ _ s _ ϖ L σ ℓ u hZ hirr hinj hs hcomp hc hc' hall hN hcc hreg hVB hgen hℓ hT
  subst hcomp
  have hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p) := fun p =>
    SetLike.ext (hreg p (push ξ' g p) rfl)
  have hconst : ∀ (o : O) (p : Cpt ξ'), algebraMap O Ω o ∈ regAt ξ' p := fun o p =>
    (ConstReg.regular_const X' Ω ξ' O s hs p o).1
  have hconn := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper X' Ω ξ' O s ϖ hirr hinj hs hc' hcc
  have hgen' : ∀ p ∈ genFibre O ξ', (pullL hr L).IsGenAt p σ := fun p hp => by
    refine isGenAt_pull hr (hgen _ fun o ho => ?_)
    have e : algebraMap ℤ Ω o = algebraMap O Ω (o : O) := by simp
    rw [e, ← unit_iff hr]
    refine hp _ fun h0 => ho ?_
    have := congrArg (algebraMap O Ω) h0
    simpa using this
  have e : (ℓ : Ω) = algebraMap O Ω ϖ * algebraMap O Ω u := by rw [hℓ, map_mul]
  have main : ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ', OrderAt (pullL hr L) σ (algebraMap O Ω ϖ) M a p := by
    rcases hT with hT | hT
    · exact hZ X' Ω ξ' O s ϖ hirr hinj hs hc' (normal_pull hr hN) hconn (pullL hr L) σ (isVB_pull hr hVB)
        (trivMod_pull hr e (hconst ϖ) (hconst u) hT) hgen'
    · exact _root_.GlobalTheory.CompanionTheory.Ar.Flat.propZ_numerical X' Ω ξ' O s ϖ hirr hinj hs hc' (normal_pull hr hN) hconn (pullL hr L) σ
        (isVB_pull hr hVB) (numTrivMod_pull hr hc' e (hconst ϖ) (hconst u) hT) hgen'
  obtain ⟨M, a, hM, H⟩ := main
  refine ⟨M, a, hM, ?_⟩
  rintro p ⟨p', hp⟩
  have : p = push ξ' g p' := Subtype.ext hp.symm
  rw [this]
  exact order_back hr (H p')

end GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleDivisibleAtPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv

theorem mem_map_of_mem_primes {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    (m : Ideal R) [hm : m.IsMaximal] (a : A)
    (h : ∀ P : Ideal A, P.IsPrime → m.map (algebraMap R A) ≤ P → a ∈ P) : a ∈ m.map (algebraMap R A) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hr : _root_.IsReduced ((R ⧸ m) ⊗[R] A) := isReduced_of_smooth_alg (R ⧸ m) _
  have hr' : _root_.IsReduced (A ⊗[R] (R ⧸ m)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R A (R ⧸ m)).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm R A (R ⧸ m)).injective
  have hq : _root_.IsReduced (A ⧸ m.map (algebraMap R A)) :=
    isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).toRingEquiv.toRingHom
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).injective
  have hrad : (m.map (algebraMap R A)).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 hq
  refine hrad ?_
  rw [Ideal.radical_eq_sInf]
  refine Ideal.mem_sInf.2 ?_
  rintro P ⟨hP, hPp⟩
  exact h P hPp hP

theorem dvd_mul_of_mem_map {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (m : Ideal R) {c e : R}
    (h : ∀ π ∈ m, e ∣ c * π) {a : A} (ha : a ∈ m.map (algebraMap R A)) :
    algebraMap R A e ∣ algebraMap R A c * a := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨π, hπ, rfl⟩ := hx
    rw [← map_mul]
    exact map_dvd _ (h π hπ)
  | zero => rw [MulZeroClass.mul_zero]; exact dvd_zero _
  | add x y _ _ hx hy => rw [mul_add]; exact dvd_add hx hy
  | smul t x _ hx => rw [smul_eq_mul, mul_left_comm]; exact hx.mul_left _

theorem mem_basicOpen_map {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : X) :
    y ∈ X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) ↔ y ∈ V ∧ y ∈ X.basicOpen f := by
  have e : X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
    Scheme.basicOpen_res X f (homOfLE h).op
  rw [e]
  rfl

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem mem_basicOpen_top_of_notMem (p : X ⟶ Sp R) (x : X) {r : R} (hx : r ∉ (p x).asIdeal) :
    x ∈ X.basicOpen ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have hmem : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    have e := basicOpen_eq_of_affine (R := CommRingCat.of R) r
    exact (congrArg (fun U : (Sp R).Opens => p x ∈ U) e).mpr hx
  rw [← Scheme.preimage_basicOpen]
  exact hmem

theorem isUnit_cst_of_notMem (p : X ⟶ Sp R) (x : X) {r : R} (hx : r ∉ (p x).asIdeal) : IsUnit (cst p x r) := by
  have hu := (Scheme.mem_basicOpen X ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) x
    (show x ∈ p ⁻¹ᵁ ⊤ from trivial)).1 (mem_basicOpen_top_of_notMem p x hx)
  rw [cst, gs_eq p x ⊤ (show p x ∈ (⊤ : (Sp R).Opens) from trivial)]
  exact hu

theorem cst_mul (p : X ⟶ Sp R) (x : X) (a b : R) : cst p x (a * b) = cst p x a * cst p x b := by
  simp only [cst, map_mul]
  exact gs_mul p x ⊤ trivial _ _

theorem exists_smul_eq_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Sp R) [Smooth p] (M : LB X) (b : Sp R), b.asIdeal.IsMaximal → ∀ u : SecMod p M, (∀ y : X, p y = b → y ∉ Out.nonzeroLocus (M := M) u) → ∀ c e : R, e ≠ 0 → (∀ π ∈ b.asIdeal, e ∣ c * π) → ∃ u' : SecMod p M, e • u' = c • u := by
  intro R _ _ X p _ M b hb u hu c e he hdiv
  have key : ∀ j, ∀ x ∈ M.U j, cst p x e ∣ gs (𝟙 X) x (M.U j) (LB.Sec.f (c • u : SecMod p M) j) := by
    intro j x hx
    rw [smul_f, gs_mul _ x _ hx, gs_constFn p _ _ x hx, Category.id_comp]
    by_cases hxb : b.asIdeal ≤ (p x).asIdeal
    ·
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := M.U j) (x := x) hx
      have hle : V ≤ M.U j := hVU
      have sm := HasRingHomProperty.appLE @Smooth p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
      have sm' : RingHom.Smooth ((p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
        RingHom.Smooth.comp
          (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective) sm
      letI := ((p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
      have : Algebra.Smooth R Γ(X, V) := sm'
      have hconst : ∀ r : R, algebraMap R Γ(X, V) r = constFn p V r := fun _ => rfl
      have hmem : (X.presheaf.map (homOfLE hle).op).hom (LB.Sec.f u j) ∈ b.asIdeal.map (algebraMap R Γ(X, V)) := by
        have := hb
        refine mem_map_of_mem_primes b.asIdeal _ fun P hP hbP => ?_
        let y : X := hV.fromSpec (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))
        have hbo : ∀ f : Γ(X, V), y ∈ X.basicOpen f ↔ f ∉ P := fun f => by
          have e := hV.fromSpec_preimage_basicOpen f
          have e' := congrArg (fun O : (Spec Γ(X, V)).Opens => (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ O) e
          exact iff_of_eq e'
        have hyV : y ∈ V := by
          have h4 : y ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
          rw [hV.range_fromSpec] at h4
          exact h4
        have hcl : p y = b := by
          have hle' : b.asIdeal ≤ (p y).asIdeal := fun π hπ => by
            by_contra hn
            have h2 := mem_basicOpen_top_of_notMem p y hn
            have h3 : y ∈ X.basicOpen (constFn p V π) := by
              have e : constFn p V π = (X.presheaf.map (homOfLE le_top).op).hom
                  ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)) := rfl
              rw [e]
              exact (mem_basicOpen_map le_top _ y).2 ⟨hyV, h2⟩
            exact (hbo _).1 h3 (hbP (Ideal.mem_map_of_mem _ hπ))
          exact PrimeSpectrum.ext (hb.eq_of_le (p y).isPrime.ne_top hle').symm
        by_contra hn
        have h1 := (hbo _).2 hn
        exact hu y hcl (TopologicalSpace.Opens.mem_iSup.2 ⟨j, ((mem_basicOpen_map hle _ y).1 h1).2⟩)
      obtain ⟨t, ht⟩ := dvd_mul_of_mem_map b.asIdeal hdiv hmem
      refine ⟨gs (𝟙 X) x V t, ?_⟩
      have e' := congrArg (gs (𝟙 X) x V) ht
      rw [hconst, hconst, gs_mul _ x _ hxV, gs_mul _ x _ hxV, gs_constFn p _ _ x hxV, gs_constFn p _ _ x hxV,
        gs_res _ x _ hxV, Category.id_comp] at e'
      exact e'
    ·
      obtain ⟨π, hπ, hπx⟩ := Set.not_subset.1 hxb
      have hunit := isUnit_cst_of_notMem p x hπx
      obtain ⟨t, ht⟩ := hdiv π hπ
      have h1 : cst p x e ∣ cst p x c * cst p x π := by
        rw [← cst_mul, ht, cst_mul]
        exact dvd_mul_right _ _
      exact ((hunit.dvd_mul_right).1 h1).mul_right _
  obtain ⟨s', hs'⟩ := exists_div_sec p he (show LB.Sec M from (c • u : SecMod p M)) key
  exact ⟨s', SecMod.ext fun j => (hs' j).symm⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv
end
end

