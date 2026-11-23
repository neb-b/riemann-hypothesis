module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMatInjective
section
noncomputable section

open NumberField GlobalTheory.BCT Matrix
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem mulMat_eq_map (a : B.A) :
    mulMat e b a = (e : K.E →+* w.adicCompletion E).mapMatrix (LinearMap.toMatrix b b (LinearMap.mulLeft K.E a)) := rfl

theorem mulMat_one : mulMat e b (1 : B.A) = 1 := by
  rw [mulMat_eq_map, LinearMap.mulLeft_one, LinearMap.toMatrix_id, map_one]

theorem mulMat_mul (a a' : B.A) : mulMat e b (a * a') = mulMat e b a * mulMat e b a' := by
  rw [mulMat_eq_map, mulMat_eq_map, mulMat_eq_map, LinearMap.mulLeft_mul, ← map_mul, ← LinearMap.toMatrix_mul]
  rfl

theorem mulMat_injective : Function.Injective (mulMat e b) := by
  intro a a' h
  have h1 : LinearMap.toMatrix b b (LinearMap.mulLeft K.E a) = LinearMap.toMatrix b b (LinearMap.mulLeft K.E a') :=
    Matrix.map_injective e.injective h
  have h2 := congrArg (fun f : B.A →ₗ[K.E] B.A => f 1) ((LinearMap.toMatrix b b).injective h1)
  simpa using h2

def mulU : B.Aˣ →* GLw m w where
  toFun a := ⟨mulMat e b a, mulMat e b ((a⁻¹ : B.Aˣ) : B.A),
    by rw [← mulMat_mul, Units.mul_inv, mulMat_one], by rw [← mulMat_mul, Units.inv_mul, mulMat_one]⟩
  map_one' := Units.ext (mulMat_one e b)
  map_mul' a a' := Units.ext (mulMat_mul e b _ _)

theorem mulU_val (a : B.Aˣ) : (mulU e b a).val = mulMat e b a := rfl

theorem mulU_injective : Function.Injective (mulU e b) :=
  fun _ _ h => Units.ext (mulMat_injective e b (congrArg Units.val h))

end GlobalTheory.TwLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSubschemeClosedBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem openSubscheme_closedFibre_lift (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R')
    (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X'.Opens)
    (hφ : Function.Surjective φ) (h : IsPullback π f' f (spMap φ)) :
    ∃ (W : X.Opens) (ρ : U.toScheme ⟶ W.toScheme), ρ ≫ W.ι = U.ι ≫ π ∧
      IsPullback ρ (U.ι ≫ f') (W.ι ≫ f) (spMap φ) := by
  have hsp : IsClosedImmersion (spMap φ) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  have hπ : IsClosedImmersion π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) h.flip hsp
  obtain ⟨t, ht, hts⟩ :=
    (IsClosedImmersion.isClosedEmbedding π).isInducing.isOpen_iff.mp U.isOpen
  let W : X.Opens := ⟨t, ht⟩
  have hW : π ⁻¹ᵁ W = U := Opens.ext hts
  subst hW
  refine ⟨W, π ∣_ W, morphismRestrict_ι π W, ?_⟩
  exact IsPullback.paste_vert (isPullback_morphismRestrict π W) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSumAtPlaceDecomposition
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold.OrbitSumGen

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ)
  (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1))

theorem posV_ne_zero (z : PosV G v β) : z.1 ≠ 0 := by
  intro h
  have := z.2
  rw [h] at this
  simp at this

def lineOf (z : Fin G.n → ℂ) (hz : z ≠ 0) : PLv G v β := Projectivization.mk ℂ z hz

def pairOfDat (d : Dat G v β) : Ys G v β x t hx Kf K' :=
  (LeftCosets.mk _ _ d.1, lineOf G v β d.2.1 (posV_ne_zero G v β d.2))

variable {G v β}

theorem smul_line_mk (y : grp G β) (z : Fin G.n → ℂ) (hz : z ≠ 0) :
    y • lineOf G v β z hz =
      lineOf G v β ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)
        (fun h => hz (toV_injective G v β y (by rw [Matrix.toLin'_apply, h, map_zero]))) := by
  change Projectivization.map _ _ (Projectivization.mk ℂ z hz) = _
  rw [Projectivization.map_mk]
  congr 1

theorem smul_line_eq_iff (y : grp G β) (z : Fin G.n → ℂ) (hz : z ≠ 0) :
    y • lineOf G v β z hz = lineOf G v β z hz ↔
      FixL G v β y z := by
  rw [smul_line_mk]
  change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _ ↔ _
  rw [Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [← hu, Units.smul_def]⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hz
      apply toV_injective G v β y
      rw [Matrix.toLin'_apply, hc, zero_smul, map_zero]
    exact ⟨Units.mk0 c hc0, by rw [Units.smul_def, Units.val_mk0, hc]⟩

theorem fixL_smul_iff (y : grp G β) (z : Fin G.n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    FixL G v β y (c • z) ↔ FixL G v β y z := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [Matrix.mulVec_smul, smul_smul] at he
    have := congrArg (fun w => c⁻¹ • w) he
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [this]
    congr 1
    field_simp
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [Matrix.mulVec_smul, he, smul_comm]⟩

variable (G v β)

theorem same_iff_smul (a b : Dat G v β) :
    Same G v β x t hx Kf K' a b ↔ ∃ y : grp G β, y • pairOfDat G v β x t hx Kf K' a = pairOfDat G v β x t hx Kf K' b := by
  constructor
  · rintro ⟨y, k, c, hk1, hk2, hc, h1, h2⟩
    refine ⟨y, Prod.ext ?_ ?_⟩
    · change y • LeftCosets.mk _ _ a.1 = LeftCosets.mk _ _ b.1
      rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk, h1]
      change (((toAfF G β x t hx).prod (toP1 G β)) y * a.1)⁻¹ * (((toAfF G β x t hx).prod (toP1 G β)) y * a.1 * k) ∈ _
      rw [inv_mul_cancel_left]
      exact Subgroup.mem_prod.2 ⟨hk1, hk2⟩
    · change y • lineOf G v β a.2.1 _ = lineOf G v β b.2.1 _
      rw [smul_line_mk]
      change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨(Units.mk0 c hc)⁻¹, ?_⟩
      rw [h2, Units.smul_def, smul_smul]
      simp [hc]
  · rintro ⟨y, hy⟩
    have h1 := congrArg Prod.fst hy
    have h2 := congrArg Prod.snd hy
    change y • LeftCosets.mk _ _ a.1 = LeftCosets.mk _ _ b.1 at h1
    change y • lineOf G v β a.2.1 _ = lineOf G v β b.2.1 _ at h2
    rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk] at h1
    rw [smul_line_mk] at h2
    change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _ at h2
    rw [Projectivization.mk_eq_mk_iff] at h2
    obtain ⟨u, hu⟩ := h2
    refine ⟨y, (((toAfF G β x t hx).prod (toP1 G β)) y * a.1)⁻¹ * b.1, ((u⁻¹ : ℂˣ) : ℂ),
      (Subgroup.mem_prod.1 h1).1, (Subgroup.mem_prod.1 h1).2, Units.ne_zero _, ?_, ?_⟩
    · exact (mul_inv_cancel_left _ _).symm
    · rw [← hu, Units.smul_def, smul_smul]
      simp

def ptsToOrbit : Pts G v β x t hx Kf K' → MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
  Quot.lift (fun d => Quotient.mk (MulAction.orbitRel (grp G β) (Ys G v β x t hx Kf K')) (pairOfDat G v β x t hx Kf K' d))
    (fun a b h => by
      obtain ⟨y, hy⟩ := (same_iff_smul G v β x t hx Kf K' a b).1 h
      exact Quotient.sound ⟨y⁻¹, show y⁻¹ • _ = _ by rw [← hy, inv_smul_smul]⟩)

theorem ptsToOrbit_eq (q : Pts G v β x t hx Kf K') :
    ptsToOrbit G v β x t hx Kf K' q = Quotient.mk _ (pairOfDat G v β x t hx Kf K' (Quot.out q)) :=
  (congrArg (ptsToOrbit G v β x t hx Kf K') (Quot.out_eq q)).symm

theorem ptsToOrbit_injective : Function.Injective (ptsToOrbit G v β x t hx Kf K') := by
  intro q₁ q₂ h
  rw [ptsToOrbit_eq, ptsToOrbit_eq] at h
  obtain ⟨g, hg⟩ := Quotient.exact h
  rw [← Quot.out_eq q₁, ← Quot.out_eq q₂]
  exact (Quot.sound ((same_iff_smul G v β x t hx Kf K' _ _).2 ⟨g, hg⟩)).symm

theorem card_stab_eq (d : Dat G v β) :
    Nat.card (Stab G v β x t hx Kf K' d) =
      Nat.card (MulAction.stabilizer (grp G β) (pairOfDat G v β x t hx Kf K' d)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [MulAction.mem_stabilizer_iff, Prod.ext_iff]
  change _ ↔ y • LeftCosets.mk _ _ d.1 = LeftCosets.mk _ _ d.1 ∧
    y • lineOf G v β d.2.1 _ = lineOf G v β d.2.1 _
  rw [smul_line_eq_iff, ← MulAction.mem_stabilizer_iff, ← stab_eq_stabilizer]
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, LeftCosets.mem_map_conj, and_assoc]

theorem cxF_pairOfDat (wt : Polynomial G.F → ℂ) (f : G.GAf → ℂ) (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (f' : Gr G 1 → ℂ) (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) (d : Dat G v β) (y : grp G β) :
    cxF G v wt β x t hx Kf f K' f' (pairOfDat G v β x t hx Kf K' d) y =
      if FixL G v β y d.2.1 then
        f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) *
          wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
      else 0 := by
  obtain ⟨k, hk, e⟩ := LeftCosets.rep_mk (ι := (toAfF G β x t hx).prod (toP1 G β)) (K := Kf.prod K') d.1
  have hz := posV_ne_zero G v β d.2
  obtain ⟨u, hu⟩ : ∃ u : ℂˣ, u • d.2.1 = Projectivization.rep (lineOf G v β d.2.1 hz) :=
    (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hz).1
      (Projectivization.mk_rep (lineOf G v β d.2.1 hz))
  have hpos : 0 < (star (Projectivization.rep (lineOf G v β d.2.1 hz)) ⬝ᵥ
      (herm G v β *ᵥ Projectivization.rep (lineOf G v β d.2.1 hz))).re := by
    rw [← hu]
    have := (pos_iff_smul_toV p G v β 1 d.2.1 u u.ne_zero).1 d.2.2
    simpa [Units.smul_def] using this
  have hfix : FixL G v β y (Projectivization.rep (lineOf G v β d.2.1 hz)) ↔ FixL G v β y d.2.1 := by
    rw [← hu, Units.smul_def]
    exact fixL_smul_iff y _ _ u.ne_zero
  simp only [cxF, pairOfDat, hpos, hfix, true_and, e, Prod.fst_mul, Prod.snd_mul]
  split_ifs with hF
  · rw [Subgroup.mem_prod] at hk
    have e1 : (d.1.1 * k.1)⁻¹ * toAfF G β x t hx y * (d.1.1 * k.1) =
        k.1⁻¹ * (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * k.1 := by group
    have e2 : (d.1.2 * k.2)⁻¹ * toP1 G β y * (d.1.2 * k.2) =
        k.2⁻¹ * (d.1.2⁻¹ * toP1 G β y * d.1.2) * k.2 := by group
    rw [e1, e2, hf _ hk.1, hf' _ hk.2]
  · rfl

end GlobalTheory.CxUnfold.OrbitSumGen

namespace GlobalTheory.CxUnfold.OrbitSumGen

end GlobalTheory.CxUnfold.OrbitSumGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalComplementHyperbolicPlaneLatticeSelfDuStatement
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalComplement_hyperbolicPlane_lattice_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E),
    (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) →
    (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    ∀ u, u ∈ lowLat ι L ↔ ∀ u' ∈ lowLat ι L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E (o * form σ (ιᵀ * J * ι.map σ) u u')) := by
  first | exact @GlobalTheory.PlaneSkewDual.lowLat_selfDual | exact GlobalTheory.PlaneSkewDual.lowLat_selfDual | (intros; apply GlobalTheory.PlaneSkewDual.lowLat_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalProjectionIntegralAdic
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory
namespace IdempotentUnimodular

theorem exists_factor {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) O) (he : e * e = e) :
    ∃ (s : ℕ) (F : Matrix (Fin n) (Fin s) O) (C : Matrix (Fin s) (Fin n) O),
      F * C = e ∧ C * F = 1 := by
  obtain ⟨s, b⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin n)) (LinearMap.range (Matrix.toLin' e))
  refine ⟨s, LinearMap.toMatrix b (Pi.basisFun O (Fin n)) (LinearMap.range (Matrix.toLin' e)).subtype,
    LinearMap.toMatrix (Pi.basisFun O (Fin n)) b (Matrix.toLin' e).rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]
    have : (LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ (Matrix.toLin' e).rangeRestrict
        = Matrix.toLin' e := by
      ext x; simp
    rw [this, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix_comp]
    have : (Matrix.toLin' e).rangeRestrict ∘ₗ (LinearMap.range (Matrix.toLin' e)).subtype
        = LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      simp [Matrix.mulVec_mulVec, he]
    rw [this, LinearMap.toMatrix_id]

theorem exists_basis {K : Type*} [Field K] (O : Subring K) [IsPrincipalIdealRing O]
    (σ : K →+* K) (hσ : ∀ x ∈ O, σ x ∈ O) {n : ℕ} (V : Submodule K (Fin n → K))
    (e : Matrix (Fin n) (Fin n) K) (hint : ∀ i j, e i j ∈ O) (h1 : ∀ x, e *ᵥ x ∈ V)
    (h2 : ∀ x ∈ V, e *ᵥ x = x) (h3 : ∀ x ∈ V, ∀ y, ∑ k, σ (x k) * (y - e *ᵥ y) k = 0) :
    ∃ (s : ℕ) (f : Module.Basis (Fin s) K V),
      (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → K) k) * (f j : Fin n → K) k).det ∈ O ∧
      ∃ d ∈ O,
        (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → K) k) * (f j : Fin n → K) k).det * d = 1 := by
  have hee : e * e = e := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    exact h2 _ (h1 x)
  let e₀ : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨e i j, hint i j⟩
  have he₀ : e₀.map O.subtype = e := by ext i j; rfl
  have hee₀ : e₀ * e₀ = e₀ := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    show (e₀ * e₀).map O.subtype = e₀.map O.subtype
    rw [Matrix.map_mul, he₀, hee]
  obtain ⟨s, F₀, C₀, hFC₀, hCF₀⟩ := exists_factor e₀ hee₀
  let σ₀ : O →+* O := (σ.comp O.subtype).codRestrict O (fun x => hσ x x.2)
  set F := F₀.map O.subtype with hF
  set C := C₀.map O.subtype with hC
  have hFC : F * C = e := by rw [hF, hC, ← Matrix.map_mul, hFC₀, he₀]
  have hCF : C * F = 1 := by
    rw [hF, hC, ← Matrix.map_mul, hCF₀]; simp
  have heF : e * F = F := by rw [← hFC, Matrix.mul_assoc, hCF, Matrix.mul_one]
  have hmem : ∀ j, (fun k => F k j) ∈ V := by
    intro j
    have : (fun k => F k j) = e *ᵥ (fun k => F k j) := by
      funext k
      conv_lhs => rw [← heF]
      rfl
    rw [this]; exact h1 _
  have hmem' : ∀ y, F *ᵥ y ∈ V := by
    intro y
    rw [← heF, ← Matrix.mulVec_mulVec]; exact h1 _
  let φ : V ≃ₗ[K] (Fin s → K) := LinearEquiv.ofLinear (Matrix.toLin' C ∘ₗ V.subtype)
    ((Matrix.toLin' F).codRestrict V (fun y => hmem' y))
    (by
      apply LinearMap.ext
      intro y
      show C *ᵥ (F *ᵥ y) = y
      rw [Matrix.mulVec_mulVec, hCF, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      show F *ᵥ (C *ᵥ (x : Fin n → K)) = x
      rw [Matrix.mulVec_mulVec, hFC, h2 _ x.2])
  have hb : ∀ i k, ((Module.Basis.ofEquivFun φ i : V) : Fin n → K) k = F k i := by
    intro i k
    rw [Module.Basis.coe_ofEquivFun]
    show (F *ᵥ (Pi.single i 1)) k = F k i
    simp
  refine ⟨s, Module.Basis.ofEquivFun φ, ?_⟩
  have hG : (Matrix.of fun i j => ∑ k, σ (((Module.Basis.ofEquivFun φ i : V) : Fin n → K) k) *
      ((Module.Basis.ofEquivFun φ j : V) : Fin n → K) k) = (F.map σ)ᵀ * F := by
    ext i j
    simp only [hb, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hG]
  have hFe : (F.map σ)ᵀ * e = (F.map σ)ᵀ := by
    ext i j
    have := h3 _ (hmem i) (Pi.single j 1)
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Matrix.mulVec_single_one,
      sub_eq_zero] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
    simpa using this.symm
  have hinv : ((F.map σ)ᵀ * F) * (C * (C.map σ)ᵀ) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc _ F, hFC, hFe, ← Matrix.transpose_mul,
      ← Matrix.map_mul, hCF]
    simp
  have hA : (F.map σ)ᵀ * F = ((F₀.map σ₀)ᵀ * F₀).map O.subtype := by
    rw [Matrix.map_mul]; rfl
  have hB : C * (C.map σ)ᵀ = (C₀ * (C₀.map σ₀)ᵀ).map O.subtype := by
    rw [Matrix.map_mul]; rfl
  refine ⟨?_, (C * (C.map σ)ᵀ).det, ?_, ?_⟩
  · rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact Subtype.property _
  · rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact Subtype.property _
  · rw [← Matrix.det_mul, hinv, Matrix.det_one]

theorem main : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    (e : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, Valued.v (e i j) ≤ 1) → (∀ x, e *ᵥ x ∈ V) →
    (∀ x ∈ V, e *ᵥ x = x) → (∀ x ∈ V, ∀ y, ∑ k, σ (x k) * (y - e *ᵥ y) k = 0) →
    ∃ (s : ℕ) (f : Module.Basis (Fin s) (w.adicCompletion E) V),
      Valued.v (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → w.adicCompletion E) k) * (f j : Fin n → w.adicCompletion E) k).det = 1 := by
  intro E _ _ w σ _ hv n V e hint h1 h2 h3
  haveI : IsPrincipalIdealRing (w.adicCompletionIntegers E).toSubring :=
    inferInstanceAs (IsPrincipalIdealRing (w.adicCompletionIntegers E))
  have hO : ∀ x, x ∈ (w.adicCompletionIntegers E).toSubring ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  obtain ⟨s, f, hd, d, hd', hdd⟩ := exists_basis (w.adicCompletionIntegers E).toSubring σ
    (fun x hx => by rw [hO] at hx ⊢; rwa [hv]) V e (fun i j => (hO _).2 (hint i j)) h1 h2 h3
  refine ⟨s, f, ?_⟩
  rw [hO] at hd hd'
  have h := congrArg Valued.v hdd
  rw [map_mul, map_one] at h
  refine le_antisymm hd ?_
  rw [← h]
  exact mul_le_of_le_one_right' hd'

end IdempotentUnimodular
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingDefiniteBaseVanishOfMiStar2
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Div

theorem pairing_definite_base_vanish_of_miStar2 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH), (R.toCx3 F).MIstar2 (F.eV (R.toCx3 F).zs) sEE → CxData.BtVanish (fc := F.fc) (R.toCx3 F) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hsep hC hP sEE hM
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP
  obtain ⟨d, hU, hI, -⟩ := hM
  exact CxData.base_tuple_vanishing_of_hypotheses _ F.cr F.cv hR.jIsoR (hR.levs true).1 (hR.levs true).2.1 (hR.levs true).2.2
    (definite_coordinates_in_good_part _ true) (EvTie.evTie_of_ok hOk F _) hU hI

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
section
open GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.ShapeSmoothFinite

theorem continuous_matCoord_ujMat {n : ℕ} (ε : Fin n → Bool) : Continuous (matCoord (ujMat ε)) :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val

theorem mem_ccMat_and_isBiFinite {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : Mat n → ℂ) (hφ : φ ∈ ShapeM ε d) :
    (fun g : UJ ε => φ (toM g)) ∈ CcMat (ujMat ε) ∧ IsBiFinite (KG ε) (fun g : UJ ε => φ (toM g)) := by
  obtain ⟨h0, hadd, hsmul⟩ := GlobalTheory.isBiFinite_subspace (UJ ε) (KG ε)
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, ⟨hH, R, hR⟩, -, rfl⟩ := h
    exact ⟨GlobalTheory.CutoffPoly.cutoff_mul_poly_mem_ccMat n ε H R hH hR P, GlobalTheory.PolyShapeFinite.main n ε H P⟩
  | zero => exact ⟨Submodule.zero_mem _, h0⟩
  | add φ ψ _ _ h h' => exact ⟨Submodule.add_mem _ h.1 h'.1, hadd _ _ h.2 h'.2⟩
  | smul c φ _ h => exact ⟨Submodule.smul_mem _ c h.1, hsmul c _ h.2⟩

theorem stShape : GlobalTheory.PsCo.Pc1.StShape := by
  intro n ε d φ hφ
  obtain ⟨h1, h2⟩ := mem_ccMat_and_isBiFinite ε d φ hφ
  exact ⟨h1, h2, continuous_of_mem_ccSmooth (continuous_matCoord_ujMat ε) h1, (mem_ccSmooth.1 h1).1⟩

end GlobalTheory.ShapeSmoothFinite
end

