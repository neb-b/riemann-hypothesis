module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFiberIsAlgebraicResidueFieldOfLft
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

namespace GlobalTheory

theorem isAlgebraic_residueField_transport {X : Scheme.{0}} {w x : X} (h : w = x) {C : CommRingCat.{0}}
    (ψ : X.residueField w ⟶ C) (φ : X.residueField x ⟶ C)
    (e : Spec.map ψ ≫ X.fromSpecResidueField w = Spec.map φ ≫ X.fromSpecResidueField x)
    (hφ : letI := φ.hom.toAlgebra; Algebra.IsAlgebraic (X.residueField x) C) :
    letI := ψ.hom.toAlgebra; Algebra.IsAlgebraic (X.residueField w) C := by
  subst h
  have : ψ = φ := Spec.map_injective ((cancel_mono _).mp e)
  subst this
  exact hφ

theorem exists_mem_fiber_isAlgebraic_residueField :
    ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧
      (letI := (π.residueFieldMap y).hom.toAlgebra;
        Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) := by
  intro Y X π _ y₀
  let x := π y₀
  let s : π.fiber x ⟶ Spec (X.residueField x) := π.fiberToSpecResidueField x
  haveI : LocallyOfFiniteType s := by
    show LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  haveI : JacobsonSpace (π.fiber x) := LocallyOfFiniteType.jacobsonSpace s
  have hx : y₀ ∈ Set.range (π.fiberι x) := by
    rw [π.range_fiberι]; rfl
  obtain ⟨y₀', -⟩ := hx
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set (π.fiber x)))
    ⟨y₀', trivial⟩ isClosed_univ.isLocallyClosed
  have h1 : LocallyOfFiniteType ((π.fiber x).fromSpecResidueField z) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hz
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((π.fiber x).fromSpecResidueField z ≫ s)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  have halg : letI := φ.hom.toAlgebra;
      Algebra.IsAlgebraic (X.residueField x) ((π.fiber x).residueField z) := by
    letI : Algebra (X.residueField x) ((π.fiber x).residueField z) := φ.hom.toAlgebra
    haveI : Algebra.FiniteType (X.residueField x) ((π.fiber x).residueField z) := hft
    haveI : Module.Finite (X.residueField x) ((π.fiber x).residueField z) :=
      finite_of_finite_type_of_isJacobsonRing _ _
    exact Algebra.IsAlgebraic.of_finite _ _
  let y : Y := π.fiberι x z
  have hy : π y = x := by
    have : y ∈ Set.range (π.fiberι x) := ⟨z, rfl⟩
    rw [π.range_fiberι] at this
    exact this
  refine ⟨y, hy, ?_⟩
  let g := (π.fiberι x).residueFieldMap z
  let ψ := π.residueFieldMap y ≫ g
  have e : Spec.map ψ ≫ X.fromSpecResidueField (π y) = Spec.map φ ≫ X.fromSpecResidueField x := by
    have e2 : π.fiberι x ≫ π = s ≫ X.fromSpecResidueField x := pullback.condition
    rw [hφ, Category.assoc, ← e2, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]
  have hψ := isAlgebraic_residueField_transport hy ψ φ e halg
  letI : Algebra (X.residueField (π y)) (Y.residueField y) := (π.residueFieldMap y).hom.toAlgebra
  letI : Algebra (Y.residueField y) ((π.fiber x).residueField z) := g.hom.toAlgebra
  letI : Algebra (X.residueField (π y)) ((π.fiber x).residueField z) := ψ.hom.toAlgebra
  haveI : IsScalarTower (X.residueField (π y)) (Y.residueField y) ((π.fiber x).residueField z) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.IsAlgebraic.tower_bot_of_injective (R := X.residueField (π y)) (A := (π.fiber x).residueField z) g.hom.injective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoHom
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.MonoHom

variable {X : Type} [AddCommGroup X] {K : Type} [Field K]

def pform {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) : LinearMap.BilinForm ℤ X :=
  (e.coord i).smulRight (e.coord j)

@[simp] theorem pform_apply {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) (x y : X) :
    pform e i j x y = e.coord i x * e.coord j y := by
  simp [pform]

end GlobalTheory.MonoHom

namespace GlobalTheory.MonoHom

end GlobalTheory.MonoHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeatPrimeLevelAutSubgroupUnipotent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep.UnipPrime

open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters Formalism.L2.Pj

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem exists_plOver (j : Fin 2) : Nonempty (PlOver D.host j) := by
  have hne : Ideal.span {((D.host.g j : ℕ) : 𝓞 D.host.F)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at h1
    have : ((D.host.g j : ℕ) : 𝓞 D.host.F) = algebraMap ℤ (𝓞 D.host.F) (D.host.g j : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank] at h1
    have hd : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
    have hg := (D.host.g_prime j).two_le
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
    have : 2 ^ Module.finrank ℚ D.host.F ≤ D.host.g j ^ Module.finrank ℚ D.host.F := Nat.pow_le_pow_left hg _
    have : 2 ≤ 2 ^ Module.finrank ℚ D.host.F := Nat.le_self_pow hd.ne' 2
    omega
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hg : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∈ P := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨⟨P, hP.isPrime, fun e => ?_⟩, hg⟩⟩
  rw [e, Ideal.mem_bot] at hg
  exact (D.host.g_prime j).ne_zero (by exact_mod_cast hg)

theorem isNilpotent_sub_one_of_unitri {r : ℕ} {k : Type} [Field k] {u : GL (Fin r) k} (hu : u ∈ unitri r k) :
    IsNilpotent ((u : Matrix (Fin r) (Fin r) k) - 1) := by
  have ht : ((u : Matrix (Fin r) (Fin r) k) - 1).BlockTriangular id := hu.1.sub Matrix.blockTriangular_one
  have hc : ((u : Matrix (Fin r) (Fin r) k) - 1).charpoly = Polynomial.X ^ r := by
    rw [Matrix.charpoly_of_upperTriangular _ ht]
    simp [hu.2]
  refine ⟨r, ?_⟩
  have := Matrix.aeval_self_charpoly ((u : Matrix (Fin r) (Fin r) k) - 1)
  rwa [hc, map_pow, Polynomial.aeval_X] at this

theorem neat_typePrime (hM : D.host.g 0 * D.host.g 1 ∣ l.M) (hg : ∀ k, Dw.p + Dw.q + 1 < D.host.g k)
    (v : Sq D.host) : NeatPrime (typePrime l v) (D.host.g v.1) (Dw.p + Dw.q) ∧ (typePrime l v).IsPrime := by
  have hP : (typePrime l v).IsPrime := by
    refine halfPrime_isPrime l v.2.1.isMaximal ?_
    obtain ⟨k, hk⟩ := (g_dvd (D := D) v.1).trans hM
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ v.2.2
  refine ⟨⟨D.host.g_prime v.1, absNorm_eq_of_split (D.host.g_prime _) (D.nd.g_split _) hP (g_mem_typePrime v),
    fun hmem => ?_, hg v.1⟩, hP⟩
  have h0 : Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime v.1).ne_zero
  have hsq : Squarefree (Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)}) :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D v.1).2
  have hd : typePrime l v * typePrime l v ∣ Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← sq]
    exact hmem
  exact hP.ne_top (Ideal.isUnit_iff.1 (hsq _ hd))

theorem unipAt_of_unitri (fr : TypeFrame Dw l) (γ : LevelAut Dw l) (v : Sq D.host)
    (hγ : typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1))) : UnipAt (typePrime l v) γ := by
  obtain ⟨n, hn⟩ := isNilpotent_sub_one_of_unitri hγ
  set Nm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)) :=
    ((typeRed fr γ v : GL (Fin D.R.r) (ZMod (D.host.g v.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) - 1
    with hNm
  let π : Dw.La →ₗ[𝓞 D.host.E] QMod Dw.La (typePrime l v) := Submodule.mkQ _
  have key : ∀ (m : ℕ) (x : Dw.La), fr v (π (((liftLa γ - 1) ^ m) x)) = (Nm ^ m).mulVec (fr v (π x)) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', ← Matrix.mulVec_mulVec, ← ih]
      generalize ((liftLa γ - 1) ^ m) x = y
      have h1 : π (liftLa γ y) = qProj (J := typePrime l v) le_sup_left
          (γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y)) := by
        rw [← liftLa_spec]; rfl
      have h2 : π y = qProj (J := typePrime l v) le_sup_left ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y) := rfl
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub, h1, h2, hNm, Matrix.sub_mulVec,
        Matrix.one_mulVec, typeRed_mulVec]
  refine ⟨n, fun x => ?_⟩
  have h := key n x
  rw [hn, Matrix.zero_mulVec, AddEquivClass.map_eq_zero_iff] at h
  exact (Submodule.Quotient.mk_eq_zero _).1 h

theorem exists_index (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)) (hS : S = grpHR fr ∨ ∃ k, S = grpGHR fr k) :
    ∃ j : Fin 2, ∀ γ ∈ S, ∀ v : Sq D.host, v.1 = j → typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1)) := by
  rcases hS with rfl | ⟨k, rfl⟩
  · exact ⟨0, fun γ hγ v _ => hγ v trivial⟩
  · refine ⟨k + 1, fun γ hγ v hv => hγ v ?_⟩
    show v.1 ≠ k
    rw [hv]; fin_cases k <;> decide

end GlobalTheory.OrbitSep.UnipPrime


open GlobalTheory.OrbitSep.UnipPrime GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters in
theorem GlobalTheory.OrbitSep.exists_neatPrime_unipAt : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H), D.host.g 0 * D.host.g 1 ∣ l.M → (∀ k, Dw.p + Dw.q + 1 < D.host.g k) → ∀ (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ (I : Ideal (𝓞 D.host.E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) ∧ l.Mb ≤ I ∧ ∀ γ ∈ S, UnipAt I γ := by
  intro D H Dw l hM hg fr S hS
  obtain ⟨j, hj⟩ := exists_index fr S hS
  obtain ⟨w⟩ := exists_plOver (D := D) j
  let v : Sq D.host := ⟨j, w⟩
  obtain ⟨hN, -⟩ := neat_typePrime (Dw := Dw) hM hg v
  exact ⟨typePrime l v, D.host.g v.1, hN, le_sup_left, fun γ hγ => unipAt_of_unitri fr γ v (hj γ hγ v rfl)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.OrdRing

section General

variable (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]

noncomputable def intRing : ValuationSubring (FractionRing R) :=
  { (algebraMap R (FractionRing R)).range with
    mem_or_inv_mem' := fun x => by
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨y, hy⟩ }

noncomputable def intEquiv : R ≃+* intRing R :=
  RingEquiv.ofBijective ((algebraMap R (FractionRing R)).codRestrict (intRing R) fun y => ⟨y, rfl⟩)
    ⟨fun a b h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h),
     fun ⟨x, ⟨y, hy⟩⟩ => ⟨y, Subtype.ext hy⟩⟩

variable {K : Type} [Field K] (φ : K →+* FractionRing R)

noncomputable def res : (intRing R).comap φ →+* R :=
  (intEquiv R).symm.toRingHom.comp (φ.restrict ((intRing R).comap φ) (intRing R) fun _ h => h)

theorem algebraMap_res (w : (intRing R).comap φ) :
    algebraMap R (FractionRing R) (res R φ w) = φ w :=
  congrArg Subtype.val ((intEquiv R).apply_symm_apply _)

theorem res_injective : Function.Injective (res R φ) := by
  intro a b h
  have := congrArg (algebraMap R (FractionRing R)) h
  rw [algebraMap_res, algebraMap_res] at this
  exact Subtype.ext (φ.injective this)

theorem dvd_of_res_dvd {x y : (intRing R).comap φ} (hy : y ≠ 0) (h : res R φ y ∣ res R φ x) :
    y ∣ x := by
  obtain ⟨c, hc⟩ := h
  have hyK : (y : K) ≠ 0 := fun h0 => hy (Subtype.ext h0)
  have hy' : algebraMap R (FractionRing R) (res R φ y) ≠ 0 := by
    rw [algebraMap_res]; exact (map_ne_zero φ).2 hyK
  have hmem : (x : K) / y ∈ (intRing R).comap φ := by
    rw [ValuationSubring.mem_comap, map_div₀, ← algebraMap_res, ← algebraMap_res, hc, map_mul,
      mul_div_cancel_left₀ _ hy']
    exact ⟨c, rfl⟩
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  show (x : K) = (y : K) * ((x : K) / y)
  field_simp

theorem isUnit_of_isUnit_res {a : (intRing R).comap φ} (h : IsUnit (res R φ a)) : IsUnit a := by
  have ha : a ≠ 0 := by rintro rfl; rw [map_zero] at h; exact not_isUnit_zero h
  refine isUnit_of_dvd_one (dvd_of_res_dvd R φ ha ?_)
  rw [map_one]; exact h.dvd

variable [IsDiscreteValuationRing R]

theorem isPrincipalIdealRing_comap : IsPrincipalIdealRing ((intRing R).comap φ) := by
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI; exact bot_isPrincipal
  obtain ⟨y0, hy0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let s : Set ((intRing R).comap φ) := {x | x ∈ I ∧ x ≠ 0}
  have hs : s.Nonempty := ⟨y0, hy0, hne⟩
  let y := Function.argminOn (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s hs
  have hy : y ∈ s := Function.argminOn_mem _ _ hs
  refine ⟨⟨y, le_antisymm ?_ ?_⟩⟩
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; exact Submodule.zero_mem _
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact dvd_of_res_dvd R φ hy.2
      (IsDiscreteValuationRing.addVal_le_iff_dvd.1 (Function.argminOn_le (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s ⟨hx, hx0⟩))
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy.1

theorem mem_of_prime {q : Ideal ((intRing R).comap φ)} (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (a : (intRing R).comap φ) : a ∈ q ↔ ¬ IsUnit (res R φ a) := by
  constructor
  · intro ha hu
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q ha (isUnit_of_isUnit_res R φ hu))
  · intro hna
    obtain ⟨y, hyq, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
    have hry : res R φ y ≠ 0 := fun h => hy0 (res_injective R φ (by rw [h, map_zero]))
    have hfin : IsDiscreteValuationRing.addVal R (res R φ y) ≠ ⊤ :=
      fun h => hry (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
    set N := (IsDiscreteValuationRing.addVal R (res R φ y)).toNat with hN
    have h1 : 1 ≤ IsDiscreteValuationRing.addVal R (res R φ a) :=
      ENat.one_le_iff_ne_zero.2 fun h => hna (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hle : IsDiscreteValuationRing.addVal R (res R φ y) ≤
        IsDiscreteValuationRing.addVal R (res R φ (a ^ N)) := by
      rw [map_pow, IsDiscreteValuationRing.addVal_pow, ← ENat.coe_toNat hfin, ← hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal R (res R φ a) := nsmul_le_nsmul_right h1 N
    have hd := dvd_of_res_dvd R φ hy0 (IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle)
    exact hq.mem_of_pow_mem N (Ideal.mem_of_dvd _ hd hyq)

end General

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

section Order

variable {B C : Type} [CommRing B] [IsDomain B] [Field C] (ev : B →+* C) (t : B)

theorem exists_pow_mul_not_dvd (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) {b : B}
    (hb : b ≠ 0) : ∃ (n : ℕ) (c : B), b = t ^ n * c ∧ ¬ t ∣ c := by
  obtain ⟨n, hn⟩ := hfin b hb
  have hf : FiniteMultiplicity t b := ⟨n, fun h => hn ((pow_dvd_pow t (Nat.le_succ n)).trans h)⟩
  obtain ⟨c, hc, hnd⟩ := hf.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, hc, hnd⟩

theorem ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) : RingHom.ker ev = Ideal.span {t} := by
  ext b; rw [RingHom.mem_ker, Ideal.mem_span_singleton, hker]

theorem map_ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker ev)) =
      Ideal.span {algebraMap B (Localization.AtPrime (RingHom.ker ev)) t} := by
  have h := congrArg (Ideal.map (algebraMap B (Localization.AtPrime (RingHom.ker ev))))
    (ker_eq_span ev t hker)
  rw [Ideal.map_span, Set.image_singleton] at h
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ev)]
  exact h

theorem isDVR (ht : t ≠ 0) (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) :
    IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker ev)) := by
  set P := RingHom.ker ev
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have ht' : algebraMap B (Localization.AtPrime P) t ≠ 0 :=
    fun h => ht (hinj (by rw [h, map_zero]))
  have htprime : Prime (algebraMap B (Localization.AtPrime P) t) := by
    rw [← Ideal.span_singleton_prime ht', ← map_ker_eq_span ev t hker]
    infer_instance
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, htprime.irreducible, fun {x} hx => ?_⟩
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
  have hb : b ≠ 0 := by rintro rfl; exact hx (IsLocalization.mk'_zero _)
  obtain ⟨n, c, rfl, hc⟩ := exists_pow_mul_not_dvd t hfin hb
  have hcP : c ∈ P.primeCompl := fun h => hc ((hker c).1 (RingHom.mem_ker.1 h))
  have hu := IsLocalization.map_units (Localization.AtPrime P) (⟨c, hcP⟩ : P.primeCompl)
  have hs := IsLocalization.map_units (Localization.AtPrime P) s
  refine ⟨n, hu.unit * hs.unit⁻¹, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, Units.val_mul, IsUnit.unit_spec, map_mul, map_pow,
    _root_.mul_assoc, _root_.mul_assoc, hs.val_inv_mul, _root_.mul_one]

noncomputable def evLoc : Localization.AtPrime (RingHom.ker ev) →+* C :=
  IsLocalization.lift (M := (RingHom.ker ev).primeCompl) (g := ev)
    fun y => isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)

theorem evLoc_algebraMap (b : B) :
    evLoc ev (algebraMap B (Localization.AtPrime (RingHom.ker ev)) b) = ev b :=
  IsLocalization.lift_eq _ _

theorem evLoc_eq_zero_iff (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (z : Localization.AtPrime (RingHom.ker ev)) : evLoc ev z = 0 ↔ ¬ IsUnit z := by
  constructor
  · intro h hu; exact (hu.map (evLoc ev)).ne_zero h
  · intro hz
    have hm : z ∈ IsLocalRing.maximalIdeal _ := hz
    rw [map_ker_eq_span ev t hker, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    rw [map_mul, evLoc_algebraMap, (hker t).2 dvd_rfl, zero_mul]

end Order

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

theorem exists_of_dvr (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (i : A →+* Ω)
    (hf : Function.Injective f) (hi : Function.Injective i)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (j : B →+* R)
    (hj : Function.Injective j) (ev' : R →+* C) (hev : ∀ b, ev' (j b) = ev b)
    (hzero : ∀ z, ev' z = 0 ↔ ¬ IsUnit z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W)
      (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C),
      Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧
      (∀ a, i₁ a ≠ 0 → IsUnit a) ∧
      ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  have hg : Function.Injective ((algebraMap R (FractionRing R)).comp (j.comp f)) :=
    (IsFractionRing.injective R (FractionRing R)).comp (hj.comp hf)
  let φ : FractionRing A →+* FractionRing R := IsFractionRing.lift hg
  let V := (intRing R).comap φ
  haveI : IsPrincipalIdealRing V := isPrincipalIdealRing_comap R φ
  have hmemA : ∀ a : A, algebraMap A (FractionRing A) a ∈ V := fun a => by
    rw [ValuationSubring.mem_comap, IsFractionRing.lift_algebraMap]
    exact ⟨j (f a), rfl⟩
  let g : A →+* V := (algebraMap A (FractionRing A)).codRestrict V hmemA
  let i₀ : V →+* Ω := (IsFractionRing.lift hi).comp V.subtype
  have hi₀ : Function.Injective i₀ := fun x y h => Subtype.ext ((IsFractionRing.lift hi).injective h)
  have hres : ∀ a : A, res R φ (g a) = j (f a) := fun a => by
    apply IsFractionRing.injective R (FractionRing R)
    rw [algebraMap_res]
    exact IsFractionRing.lift_algebraMap hg a
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, g, i₀,
    ev'.comp (res R φ), hi₀, ?_, ?_, ?_, ?_⟩
  · ext a
    exact IsFractionRing.lift_algebraMap hi a
  · ext a
    simp only [RingHom.comp_apply]
    rw [hres, hev]
  · intro a ha
    exact isUnit_of_isUnit_res R φ (not_not.1 fun h => ha ((hzero _).2 h))
  · intro q hq
    by_cases hq0 : q = ⊥
    · left; rw [hq0, (RingHom.injective_iff_ker_eq_bot _).1 hi₀]
    · right
      ext a
      rw [mem_of_prime R φ hq hq0, RingHom.mem_ker, RingHom.comp_apply, hzero]

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow


open GlobalTheory.MBLow.OrdRing in
theorem exists_localRing_of_order : ∀ (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (t : B) (i : A →+* Ω), Function.Injective f → Function.Injective i → t ≠ 0 → (∀ b, ev b = 0 ↔ t ∣ b) → (∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C), Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  intro A B C Ω _ _ _ _ _ _ f ev t i hf hi ht hker hfin
  haveI := isDVR ev t ht hker hfin
  exact exists_of_dvr A B C Ω f ev i hf hi (Localization.AtPrime (RingHom.ker ev))
    (algebraMap B _) (IsLocalization.injective _ (RingHom.ker ev).primeCompl_le_nonZeroDivisors)
    (evLoc ev) (evLoc_algebraMap ev) (evLoc_eq_zero_iff ev t hker)

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlopeStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), HasPhi y φ → ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ r : ℕ, r ≤ Module.finrank ℚ E * Dw.q ∧ ShortBasis Q r ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * (r : ℝ) ^ 3 * φ) (2 * Real.sqrt r) := by
  first | exact @GlobalTheory.ShortPhi.exists_shortBasis | exact GlobalTheory.ShortPhi.exists_shortBasis | (intros; apply GlobalTheory.ShortPhi.exists_shortBasis <;> assumption)
end

