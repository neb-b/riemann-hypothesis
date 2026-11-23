module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalRingCardinality.DataRRMetric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTwistCharacterUnitsModSpecialIdeal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetOfSplitDetermines
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev IsDedekindDomain NumberField Polynomial
open scoped Pointwise

namespace GlobalTheory.PartsCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section Poly

variable {K L : Type} [Field K] [Field L]

theorem dualPoly_comp {a : K} (ha : a ≠ 0) (s : K) (p : K[X]) :
    dualPoly s (p.comp (C a⁻¹ * X)) = dualPoly (s * a) p := by
  have hd : (p.comp (C a⁻¹ * X)).natDegree = p.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero ha), mul_one]
  have hl : (p.comp (C a⁻¹ * X)).leadingCoeff = p.leadingCoeff * a⁻¹ ^ p.natDegree := by
    rw [leadingCoeff, hd, comp_C_mul_X_coeff, leadingCoeff]
  ext i
  by_cases hi : i ≤ p.natDegree
  · rw [coeff_dualPoly_of_le _ _ (hd ▸ hi), coeff_dualPoly_of_le _ _ hi, hl, hd, comp_C_mul_X_coeff]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi
    rw [hj, Nat.add_sub_cancel_left, pow_add, mul_pow]
    have h1 : a⁻¹ ^ i * a ^ i = 1 := by rw [← mul_pow, inv_mul_cancel₀ ha, one_pow]
    have h2 : a⁻¹ ^ j ≠ 0 := pow_ne_zero _ (inv_ne_zero ha)
    have h3 : (a⁻¹ ^ i)⁻¹ = a ^ i := by rw [inv_pow, inv_inv]
    rw [mul_inv, mul_inv, h3]
    field_simp
  · have hi' := not_le.1 hi
    rw [coeff_dualPoly_of_lt _ _ (hd ▸ hi'), coeff_dualPoly_of_lt _ _ hi']

theorem coeff_heckePolyOf (n q : ℕ) (a : ℕ → K) (i : ℕ) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i =
      if i ≤ n then (-1) ^ i * (q : K) ^ (i * (i - 1) / 2) * a i else 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
    Nat.lt_succ_iff]

theorem tri_add (i j : ℕ) : (i + j) * (i + j - 1) / 2 + i * (i - 1) / 2 = j * (j - 1) / 2 + (i + j - 1) * i := by
  have h : ∀ n : ℕ, 2 * (n * (n - 1) / 2) + n = n * n := by
    intro n
    rw [Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
    cases n with
    | zero => rfl
    | succ m => simp; ring
  have h1 := h (i + j)
  have h2 := h i
  have h3 := h j
  have h4 : (i + j - 1) * i + i = (i + j) * i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have : m + 1 + j - 1 = m + j := by omega
      rw [this]; ring
  nlinarith

theorem heckePolyOf_dual {n q : ℕ} (hq : (q : K) ≠ 0) {a b : ℕ → K} (h0 : a 0 = 1)
    (h : ∀ k ≤ n, a n * b k = a (n - k)) :
    Formalism.L2.Col.heckePolyOf n q b = dualPoly ((q : K) ^ (n - 1)) (Formalism.L2.Col.heckePolyOf n q a) := by
  have hn : a n ≠ 0 := by
    have := h n le_rfl
    rw [Nat.sub_self, h0] at this
    exact left_ne_zero_of_mul_eq_one this
  have htop : (Formalism.L2.Col.heckePolyOf n q a).coeff n ≠ 0 := by
    rw [coeff_heckePolyOf, if_pos le_rfl]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ hq)) hn
  have hd : (Formalism.L2.Col.heckePolyOf n q a).natDegree = n :=
    le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun i hi => by rw [coeff_heckePolyOf, if_neg (not_le.2 hi)])
      (le_natDegree_of_ne_zero htop)
  ext i
  by_cases hi : i ≤ n
  · rw [coeff_dualPoly_of_le _ _ (by rw [hd]; exact hi), leadingCoeff, hd, eq_inv_mul_iff_mul_eq₀ htop,
      coeff_heckePolyOf, coeff_heckePolyOf, coeff_heckePolyOf, if_pos le_rfl, if_pos hi, if_pos (Nat.sub_le _ _),
      ← h i hi]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_sub_cancel_left, ← pow_mul]
    have e := congrArg (fun m => (q : K) ^ m) (tri_add i j)
    simp only [pow_add] at e
    have e2 : ((-1 : K) ^ i) * (-1) ^ i = 1 := by rw [← mul_pow]; simp
    rw [pow_add]
    linear_combination ((-1 : K) ^ j * a (i + j) * b i * ((-1) ^ i * (-1) ^ i)) * e +
      ((-1 : K) ^ j * a (i + j) * b i * ((q : K) ^ (j * (j - 1) / 2) * (q : K) ^ ((i + j - 1) * i))) * e2
  · rw [coeff_dualPoly_of_lt _ _ (by rw [hd]; exact not_le.1 hi), coeff_heckePolyOf, if_neg hi]

end Poly

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Label

variable {R : RealDat D A Ks} {F : Face D A} {s : ℕ} (hs : A.fam.Ok s) (h : R.Char F)
include hs h

variable {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D} {jE : D.what₂.EE →ₗ[ℂ] R.HE.H}
  {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Label

section Ties

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D}
  {jE : D.what₂.EE →ₗ[ℂ] R.HE.H} {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Ties

section Main

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X}

end Main

end GlobalTheory.PartsCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusTangentVectorsAddMonoidHom
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory
section
attribute [local instance] Over.cartesianMonoidalCategory
namespace TorusTangent

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

def epsUnit (a : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr a
  inv := 1 - TrivSqZeroExt.inr a
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem epsUnit_add (a b : k) : epsUnit (a + b) = epsUnit a * epsUnit b := by
  ext <;> simp [epsUnit, add_comm]

theorem natur {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f x) := by
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  exact (congrArg (fun g => g.hom x) this).symm

noncomputable def phi (l : X →+ k) : Multiplicative X →* Γ((epsPt (𝟙 (Sp k))).left, ⊤)ˣ :=
  (Units.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom.toMonoidHom).comp
    { toFun := fun χ => epsUnit (l χ.toAdd)
      map_one' := by ext <;> simp [epsUnit]
      map_mul' := fun a b => by rw [toAdd_mul, map_add (f := _), epsUnit_add] }

noncomputable def tanPt (l : X →+ k) : epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X :=
  (splitTorusPointsEquiv (Sp k) X (epsPt (𝟙 (Sp k)))).symm (phi l)

theorem chV_tanPt (l : X →+ k) (χ : X) :
    (chV (tanPt l) χ).val = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
      (1 + TrivSqZeroExt.inr (l χ)) := by
  show ((splitTorusPointsEquiv _ _ _) ((splitTorusPointsEquiv _ _ _).symm (phi l))
    (Multiplicative.ofAdd χ)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem chV_comp {Z Z' : Over (Sp k)} (j : Z' ⟶ Z) (t : Z ⟶ splitTorus (Sp k) X) (χ : X) :
    (chV (j ≫ t) χ).val = j.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

theorem ext_val {Z : Over (Sp k)} {a b : Z ⟶ splitTorus (Sp k) X}
    (h : ∀ χ, (chV a χ).val = (chV b χ).val) : a = b :=
  TorusOfCharMap.ext_chV fun χ => Units.ext (h χ)

end TorusTangent
end


open TorusTangent in
theorem splitTorus_tangent_addHom : ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X], ∃ U : (X →+ k) → (epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ (τ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X) (ρ : X →+ X), (∀ χ, chV τ χ = charUnit (Sp k) X (ρ χ)) → ∀ l, U l ≫ τ = U (l.comp ρ) := by
  intro k _ X _
  have hΓ := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm.injective
  refine ⟨tanPt, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' h
    ext χ
    have e := congrArg (fun t => (chV t χ).val) h
    simp only [chV_tanPt] at e
    have e2 := congrArg TrivSqZeroExt.snd (hΓ e)
    simpa using e2
  · intro l
    let j : Over.mk (𝟙 (Sp k)) ⟶ epsPt (𝟙 (Sp k)) :=
      Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
        simp only [Over.mk_hom, Category.comp_id]
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1)
    have : j ≫ tanPt l = 1 := by
      refine ext_val fun χ => ?_
      rw [chV_comp, chV_tanPt]
      simp only [j, Over.homMk_left]
      rw [natur]
      simp [chV, map_one]
    exact congrArg CommaMorphism.left this
  · intro l l'
    show (splitTorusPointsEquiv _ _ _).symm _ =
      (splitTorusPointsEquiv _ _ _).symm (phi l) * (splitTorusPointsEquiv _ _ _).symm (phi l')
    rw [← map_mul]
    congr 1
    ext χ
    simp [phi, epsUnit_add]
  · intro t l
    let s : epsPt (𝟙 (Sp k)) ⟶ epsPt (𝟙 (Sp k)) :=
      Over.homMk (spMap (epsScale t)) (by
        simp only [Over.mk_hom, Category.comp_id]
        rw [← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change epsScale t (algebraMap k (DualNumber k) x) = algebraMap k (DualNumber k) x
        ext <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl])
    have : tanPt ((AddMonoidHom.mulLeft t).comp l) = s ≫ tanPt l := by
      refine ext_val fun χ => ?_
      rw [chV_comp, chV_tanPt, chV_tanPt]
      simp only [s, Over.homMk_left]
      rw [natur]
      congr 1
      ext <;> simp [epsScale, mul_comm]
    rw [this]
    rfl
  · intro τ ρ hτ l
    have hm := ((splitTorus_map_of_charHom (Sp k) X X ρ).2 τ hτ).2.2
    refine ext_val fun χ => ?_
    rw [hm, chV_tanPt, chV_tanPt]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsetOfForallPtMem
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Adelic

theorem subset_of_forall_pt_mem : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → ∀ (Ω : Type) [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω] (Z : Set S.Y), IsClosed Z → ∀ U : Set S.Y, IsOpen U →
    (∀ x : S.Pt Ω, ptOf x.1 ∈ Z → ptOf x.1 ∈ U) → Z ⊆ U := by
  intro k _ S hS Ω _ _ _ Z hZ U hU h
  haveI := hS.smooth
  haveI : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  haveI : LocallyOfFiniteType S.str := inferInstance
  haveI : JacobsonSpace S.Y := LocallyOfFiniteType.jacobsonSpace S.str
  by_contra hne
  obtain ⟨z, hzZ, hzU⟩ := Set.not_subset.1 hne
  obtain ⟨y, ⟨hyZ, hyU⟩, hy⟩ := nonempty_inter_closedPoints (Z := Z ∩ Uᶜ) ⟨z, hzZ, hzU⟩
    (hZ.inter hU.isClosed_compl).isLocallyClosed
  have hyc : IsClosed ({y} : Set S.Y) := hy
  haveI : IsFinite (resPt y ≫ S.str) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hyc
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    unfold resPt
    infer_instance
  have hφ : (S.baseHom (resPt y)).IsIntegral := by
    have : IsIntegralHom (Spec.map (Spec.preimage (resPt y ≫ S.str))) := by
      rw [Spec.map_preimage]; infer_instance
    rw [IsIntegralHom.SpecMap_iff] at this
    exact this
  letI : Algebra k (S.Y.residueField y) := (S.baseHom (resPt y)).toAlgebra
  haveI : Algebra.IsIntegral k (S.Y.residueField y) := ⟨hφ⟩
  let τ : S.Y.residueField y →ₐ[k] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let x : S.Pt Ω := ⟨spMap τ.toRingHom ≫ resPt y, by
    rw [Category.assoc, S.comp_str, ← Spec.map_comp]
    congr 1
    ext a
    exact τ.commutes a⟩
  have hx : ptOf x.1 = y := (ptOf_spMap_comp _ _).trans (ptOf_resPt y)
  exact hyU (hx ▸ h x (hx.symm ▸ hyZ))

end GlobalTheory.Adelic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameCharacterFromProduct
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare.TameConj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions (idealHat CongMod)
open GlobalTheory.IdemSupport (mem_intAE_iff parts_cA finPart_cA_mem)

variable {D : D7}

theorem mul_mem_intAE {y z : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) (hz : z ∈ intAE D) :
    y * z ∈ intAE D := by
  rw [mem_intAE_iff] at hy hz ⊢
  rw [RingHom.map_mul]
  exact mul_mem hy hz

theorem FinUnit_mul {x y : (AE D)ˣ} (hx : FinUnit x) (hy : FinUnit y) : FinUnit (x * y) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, RingHom.map_mul, hx.1, hy.1, one_mul]
  · rw [Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.1 hy.2.1
  · rw [mul_inv, Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.2 hy.2.2

theorem FinUnit_inv {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit x⁻¹ := by
  refine ⟨?_, hx.2.2, hx.2.1⟩
  have e : infPart D (x : AE D) * infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  rwa [hx.1, one_mul] at e

theorem FinUnit_conj {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit (Units.map (cA D).toMonoidHom x) := by
  refine ⟨?_, finPart_cA_mem hx.2.1, finPart_cA_mem hx.2.2⟩
  exact (parts_cA (x : AE D)).1.trans (by rw [hx.1, RingHom.map_one])


end GlobalTheory.GeoActCompare.TameConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TanScalDecomp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieCoordMult

theorem tanScal_decomp : ∀ (O : Type) [Ring O] (F' : Type) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (act : OActN O G) (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (n a : ℕ) (T : (Fin n → R') → (epsPtR x ⟶ G)) (A : O → Matrix (Fin n) (Fin n) R') (emb : F' → O) (ω : F') (l : R') (χ : Fin a → F' → R'), Function.Injective T → (∀ v : epsPtR x ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → (∀ b c, T c ≫ act.act b = T (A b *ᵥ c)) → (∀ y : Fin n → R', A (emb ω) *ᵥ y = l • y → ∃ z : Fin a → Fin n → R', (∀ i c, A (emb c) *ᵥ z i = χ i c • z i) ∧ y = ∑ i, z i) → ∀ v : epsPtR x ⟶ G, IsTanScal act x (emb ω) l v → ∃ w : Fin a → (epsPtR x ⟶ G), (∀ i c, IsTanScal act x (emb c) (χ i c) (w i)) ∧ v = (List.ofFn w).prod := by
  intro O _ F' S G _ _ act R' _ x n a T A emb ω l χ hinj htan hadd hsc hact hdec v hv
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → R')), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ (b : O) (c : R') (w : epsPtR x ⟶ G), IsTanScal act x b c w ↔ ∃ y, A b *ᵥ y = c • y ∧ w = T y := by
    intro b c w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := (htan w).1 h1
      refine ⟨y, hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2, hsc]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(htan _).2 ⟨y, rfl⟩, ?_⟩
      rw [hact, hy, hsc]
  obtain ⟨y, hy, rfl⟩ := (eig _ _ _).1 hv
  obtain ⟨z, hz, rfl⟩ := hdec y hy
  exact ⟨fun i => T (z i), fun i c => (eig _ _ _).2 ⟨z i, hz i c, rfl⟩, (Tsum a z).symm⟩

end GlobalTheory.LieCoordMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypeCharacterConjugateInverse
section
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.TypeCharacterConjugateInverse

theorem toSquareBlock_mul_of_blockTriangular {r : ℕ} {k : Type} [Field k] {A B : Matrix (Fin r) (Fin r) k}
    {b : Fin r → Fin r} (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (c : Fin r)
    [Fintype {i : Fin r // b i = c}] :
    A.toSquareBlock b c * B.toSquareBlock b c = (A * B).toSquareBlock b c := by
  classical
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.mul_apply, Matrix.of_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun l => b l = c) (p := fun l => b l = c) (by simp)
    (fun l => A i.1 l * B l j.1)]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_
  have hl' : b l ≠ c := by simpa using hl
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hA (show b l < b i.1 by rw [i.2]; exact h), zero_mul]
  · rw [hB (show b j.1 < b l by rw [j.2]; exact h), mul_zero]

theorem blockTriangular_inv {r : ℕ} {k : Type} [Field k] {b : Fin r → Fin r} (z : GL (Fin r) k)
    (hz : (z : Matrix (Fin r) (Fin r) k).BlockTriangular b) :
    ((z⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).BlockTriangular b := by
  letI := z.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hz

theorem toSquareBlock_mul_inv {r : ℕ} {k : Type} [Field k] {b : Fin r → Fin r} (z : GL (Fin r) k)
    (hz : (z : Matrix (Fin r) (Fin r) k).BlockTriangular b) (c : Fin r)
    [Fintype {i : Fin r // b i = c}] [DecidableEq {i : Fin r // b i = c}] :
    (z : Matrix (Fin r) (Fin r) k).toSquareBlock b c *
      ((z⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).toSquareBlock b c = 1 := by
  rw [toSquareBlock_mul_of_blockTriangular hz (blockTriangular_inv z hz), ← Units.val_mul, mul_inv_cancel,
    Units.val_one]
  ext i j
  simp [Matrix.toSquareBlock_def, Matrix.one_apply, Subtype.ext_iff]

theorem typeChar_conj_inv : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (r : ℕ) (s : LevelCuspCharacters.SSParam p K r),
    (∀ x y : GL (Fin r) (ZMod p), IsConj x y → LevelCuspCharacters.typeChar s x = LevelCuspCharacters.typeChar s y) ∧
    ∀ x : GL (Fin r) (ZMod p),
      LevelCuspCharacters.typeChar (⟨s.1, fun c => (s.2 c)⁻¹⟩ : LevelCuspCharacters.SSParam p K r) x = LevelCuspCharacters.typeChar s x⁻¹ := by
  intro p _ K _ r s
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    unfold LevelCuspCharacters.typeChar
    congr 1
    letI := Fintype.ofFinite (GL (Fin r) (ZMod p))
    refine Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun y => ?_
    have h : (Equiv.mulLeft c y)⁻¹ * (c * x * c⁻¹) * (Equiv.mulLeft c y) = y⁻¹ * x * y := by
      simp only [Equiv.coe_mulLeft]
      group
    rw [h]
  · unfold LevelCuspCharacters.typeChar
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    have h : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    rw [h]
    generalize y⁻¹ * x * y = z
    by_cases hz : (z : Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1
    · rw [if_pos hz, if_pos (blockTriangular_inv z hz)]
      refine Finset.prod_congr rfl fun c _ => ?_
      exact _root_.GlobalTheory.CuspInv.cuspChar_inv p K _ (s.2 c) _ _ (toSquareBlock_mul_inv z hz c.1)
    · rw [if_neg hz, if_neg fun h' => hz (by simpa using blockTriangular_inv z⁻¹ h')]

end GlobalTheory.TypeCharacterConjugateInverse
end

