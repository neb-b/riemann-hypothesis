module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalEigenvectorGeneratesIrreducibleSubrepre
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.InvPairing

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type} [AddCommGroup W] [Module ℂ W]

def stab {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_fixed_iff (σ : Representation ℂ G W) (H : Subgroup G) (v : W) :
    v ∈ GlobalTheory.PRep.fixed σ H ↔ ∀ h ∈ H, σ h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    simpa using hv h h.2

theorem exists_fixed_avg (σ : Representation ℂ G W) (hs : GlobalTheory.PRep.IsSmooth σ) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (x : W) :
    ∃ x₀ ∈ GlobalTheory.PRep.fixed σ K, ∀ ℓ : W →ₗ[ℂ] ℂ, (∀ k ∈ K, ∀ v, ℓ (σ k v) = ℓ v) → ℓ x = ℓ x₀ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hSo : IsOpen ((stab σ x : Subgroup G) : Set G) := hs x
  haveI : Finite (K ⧸ (stab σ x).subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hSo.preimage continuous_subtype_val)
  let f : K ⧸ (stab σ x).subgroupOf K → W := fun q => Quotient.liftOn' q (fun k : K => σ k x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    change σ ((a : G)⁻¹ * b) x = x at hab
    show σ a x = σ b x
    calc σ a x = σ a (σ ((a : G)⁻¹ * b) x) := by rw [hab]
      _ = σ b x := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left])
  have hrange : Set.range f = Set.range (fun k : K => σ k x) := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H k => exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨QuotientGroup.mk k, rfl⟩
  have hfin : (Set.range (fun k : K => σ k x)).Finite := hrange ▸ Set.finite_range f
  set O := hfin.toFinset with hO
  have hxO : x ∈ O := by
    rw [hO, Set.Finite.mem_toFinset]
    exact ⟨1, by simp⟩
  have hperm : ∀ k ∈ K, ∑ v ∈ O, σ k v = ∑ v ∈ O, v := by
    intro k hk
    refine Finset.sum_nbij' (fun v => σ k v) (fun v => σ k⁻¹ v) ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv ⊢
      obtain ⟨j, rfl⟩ := hv
      exact ⟨⟨k, hk⟩ * j, by simp [Module.End.mul_apply]⟩
    · intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv ⊢
      obtain ⟨j, rfl⟩ := hv
      exact ⟨⟨k, hk⟩⁻¹ * j, by simp [Module.End.mul_apply]⟩
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro v _
      rfl
  refine ⟨((O.card : ℂ))⁻¹ • ∑ v ∈ O, v, ?_, ?_⟩
  · rw [mem_fixed_iff]
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, hperm k hk]
  · intro ℓ hℓ
    have hconst : ∀ v ∈ O, ℓ v = ℓ x := by
      intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv
      obtain ⟨j, rfl⟩ := hv
      exact hℓ j j.2 x
    have hcard : (O.card : ℂ) ≠ 0 := by
      have : 0 < O.card := Finset.card_pos.mpr ⟨x, hxO⟩
      exact_mod_cast this.ne'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem exists_rep (U : Submodule ℂ W) [FiniteDimensional ℂ U]
    (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (hB : ∀ x, x ≠ 0 → 0 < (B x x).re) (f : U →ₗ[ℂ] ℂ) :
    ∃ z : U, ∀ x : U, f x = B x z := by
  let T : U →ₗ[ℝ] Module.Dual ℂ U :=
    { toFun := fun z => (B.flip (z : W)).comp U.subtype
      map_add' := by intro a b; ext x; simp
      map_smul' := by
        intro r z
        ext x
        simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.flip_apply,
          Submodule.coe_smul]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r z, Submodule.coe_smul, LinearMap.map_smulₛₗ, Complex.real_smul,
          RCLike.conj_ofReal, smul_eq_mul]
        rfl }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hne
    have h1 : B z z = 0 := by
      have := LinearMap.congr_fun hz z
      simpa [T] using this
    have := hB z (fun h => hne (Subtype.ext h))
    rw [h1] at this
    simp at this
  have hrank : Module.finrank ℝ U = Module.finrank ℝ (Module.Dual ℂ U) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ U, ← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ U),
      Subspace.dual_finrank_eq]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  obtain ⟨z, hz⟩ := hsurj f
  exact ⟨z, fun x => by rw [← hz]; rfl⟩

end GlobalTheory.InvPairing

namespace GlobalTheory.InvPairing

theorem exists_intertwiner : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ G W) (σ' : Representation ℂ G W'), IsAdmissible σ → GlobalTheory.PRep.IsSmooth σ' → ∀ (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ), (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ g x y, B (σ g x) (σ g y) = B x y) → (∀ g x y, C (σ g x) (σ' g y) = C x y) → ∃ φ : W' →ₗ[ℂ] W, (∀ g y, φ (σ' g y) = σ g (φ y)) ∧ ∀ x y, C x y = B x (φ y) := by
  intro G _ _ _ K hKo hKc W W' _ _ _ _ σ σ' hσ hσ' B C hB hBinv hCinv
  have huniq : ∀ z z' : W, (∀ x, B x z = B x z') → z = z' := by
    intro z z' h
    by_contra hne
    have hne' : z - z' ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hB _ hne'
    have h0 : B (z - z') (z - z') = 0 := by rw [map_sub (B (z - z')), h (z - z'), sub_self]
    rw [h0] at hpos
    simp at hpos
  have hex : ∀ y, ∃ z, ∀ x, C x y = B x z := by
    intro y
    set K' := K ⊓ stab σ' y with hK'
    have hSo : IsOpen ((stab σ' y : Subgroup G) : Set G) := hσ' y
    have hKo' : IsOpen (K' : Set G) := hKo.inter hSo
    have hKc' : IsCompact (K' : Set G) := hKc.inter_right (Subgroup.isClosed_of_isOpen _ hSo)
    haveI := hσ.2 K' hKo' hKc'
    obtain ⟨z, hz⟩ := exists_rep (GlobalTheory.PRep.fixed σ K') B hB ((C.flip y).comp (GlobalTheory.PRep.fixed σ K').subtype)
    refine ⟨z, fun x => ?_⟩
    obtain ⟨x₀, hx₀, hℓ⟩ := exists_fixed_avg σ hσ.1 K' hKc' x
    have e1 := hℓ (C.flip y) (fun k hk v => by
      have hy : σ' k y = y := (Subgroup.mem_inf.mp hk).2
      simp only [LinearMap.flip_apply]
      conv_lhs => rw [← hy]
      exact hCinv k v y)
    have e2 := hℓ (B.flip z) (fun k hk v => by
      have hz' : σ k z = z := (mem_fixed_iff σ K' z).mp z.2 k hk
      simp only [LinearMap.flip_apply]
      conv_lhs => rw [← hz']
      exact hBinv k v z)
    simp only [LinearMap.flip_apply] at e1 e2
    rw [e1, e2]
    exact hz ⟨x₀, hx₀⟩
  choose φ₀ hφ₀ using hex
  refine ⟨{ toFun := φ₀, map_add' := ?_, map_smul' := ?_ }, ?_, fun x y => hφ₀ y x⟩
  · intro a b
    apply huniq
    intro x
    rw [map_add (B x), ← hφ₀, ← hφ₀, ← hφ₀, map_add (f := _)]
  · intro c a
    apply huniq
    intro x
    rw [RingHom.id_apply, LinearMap.map_smulₛₗ (B x), ← hφ₀, ← hφ₀, LinearMap.map_smulₛₗ]
  · intro g y
    apply huniq
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← hφ₀]
    have hx : x = σ g (σ g⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hx, hCinv, hBinv]
    exact hφ₀ y _

end GlobalTheory.InvPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalUnitaryGroupIsoConjIsometry
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocIsoConj

open Formalism.UG

theorem conj_unitary {R : Type} [CommRing R] (σ : R →+* R) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) (g : Matrix n n R)
    (hg : cT σ g * J * g = J) : cT σ (a * g * b) * J' * (a * g * b) = J' := by
  calc cT σ (a * g * b) * J' * (a * g * b) = cT σ b * (cT σ g * (cT σ a * J' * a) * g) * b := by
        rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT σ b * (cT σ a * J' * a) * b := by rw [hJ, hg]
    _ = cT σ (a * b) * J' * (a * b) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]

def conjHom {R : Type} [CommRing R] {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1) :
    Matrix n n R →* Matrix m m R where
  toFun g := a * g * b
  map_one' := by rw [Matrix.mul_one, hab]
  map_mul' g h := by
    calc a * (g * h) * b = a * g * (b * a) * h * b := by rw [hba, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_equiv {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (σ : R →+* R)
    {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) :
    ∃ φ : UJ σ J ≃ₜ* UJ σ J', ∀ g, ((φ g).1 : Matrix m m R) = a * (g.1 : Matrix n n R) * b := by
  have hJ' : cT σ b * J * b = J' := by
    rw [← hJ]
    calc cT σ b * (cT σ a * J' * a) * b = cT σ (a * b) * J' * (a * b) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hc : ∀ {k l : Type} [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l] (x : Matrix l k R)
      (y : Matrix k l R), Continuous fun g : Matrix k k R => x * g * y := by
    intro k l _ _ _ _ x y
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let φ₀ : UJ σ J →* GL m R := (Units.map (conjHom a b hab hba)).comp (UJ σ J).subtype
  let ψ₀ : UJ σ J' →* GL n R := (Units.map (conjHom b a hba hab)).comp (UJ σ J').subtype
  have hφU : ∀ g, φ₀ g ∈ UJ σ J' := fun g => conj_unitary σ a b hab J J' hJ _ g.2
  have hψU : ∀ g, ψ₀ g ∈ UJ σ J := fun g => conj_unitary σ b a hba J' J hJ' _ g.2
  let φ : UJ σ J →* UJ σ J' := φ₀.codRestrict _ hφU
  let ψ : UJ σ J' →* UJ σ J := ψ₀.codRestrict _ hψU
  have hφc : Continuous φ :=
    ((Continuous.units_map _ (hc a b)).comp continuous_subtype_val).subtype_mk _
  have hψc : Continuous ψ :=
    ((Continuous.units_map _ (hc b a)).comp continuous_subtype_val).subtype_mk _
  have l : ∀ g, ψ (φ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show b * (a * (g.1 : Matrix n n R) * b) * a = g.1
    calc b * (a * (g.1 : Matrix n n R) * b) * a = (b * a) * (g.1 : Matrix n n R) * (b * a) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hba, Matrix.one_mul, Matrix.mul_one]
  have r : ∀ g, φ (ψ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show a * (b * (g.1 : Matrix m m R) * a) * b = g.1
    calc a * (b * (g.1 : Matrix m m R) * a) * b = (a * b) * (g.1 : Matrix m m R) * (a * b) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hab, Matrix.one_mul, Matrix.mul_one]
  exact ⟨{ toFun := φ, invFun := ψ, left_inv := l, right_inv := r, map_mul' := map_mul φ,
            continuous_toFun := hφc, continuous_invFun := hψc }, fun g => rfl⟩

theorem exists_locIso : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E) (v : HeightOneSpectrum (𝓞 F)) (a : Matrix (Fin r') (Fin r) (Fv F v ⊗[F] E)) (b : Matrix (Fin r) (Fin r') (Fv F v ⊗[F] E)), a * b = 1 → b * a = 1 → Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a * JR (F := F) (Fv F v) J' * a = JR (F := F) (Fv F v) J → ∃ φ : GLoc σ J v ≃ₜ* GLoc σ J' v, ∀ g, (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val = a * (GlobalTheory.AdelicU.matHom _ σ J g).val * b := by
  intro F E _ _ _ _ _ σ r r' J J' v a b hab hba hJ
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨φ, hφ⟩ := exists_equiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a b hab hba _ _ hJ
  exact ⟨φ, hφ⟩

end GlobalTheory.LocIsoConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPowArchProjNotMemOfEigenvalueTwo
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Twist

open scoped TensorProduct Matrix


set_option maxHeartbeats 1600000 in
theorem exists_pow_projArch_not_mem_of_eigen_two : ∀ (D : D7) (V : HSp D) (g : GF V) (x : V.V), x ≠ 0 → GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x → ∀ (w : InfinitePlace D.host.F) (K : Set (GArch D.sp.cm.sig V.gram w)), IsCompact K → ∃ n : ℕ, projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) ∉ K := by
  intro D V g x hx hg w K hK
  classical
  set c : Fin V.rank → D.host.E := ⇑(V.frame.repr x) with hc_def
  have hM : (g.1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) • c := by
    have h1 := congrArg (fun y => ⇑(V.frame.repr y)) hg
    simp only [GlobalTheory.Cusp.ratAct, map_smul, Finsupp.coe_smul] at h1
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, LinearMap.toMatrix_toLin] at h1
    exact h1
  have hMn : ∀ n : ℕ, ((g ^ n).1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) ^ n • c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    have : V.frame.repr x = 0 := Finsupp.ext h
    simpa using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual D.host.F D.host.E, φ (c j) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hj ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)

  let ι : D.host.E →+* w.Completion ⊗[D.host.F] D.host.E := inclR (F := D.host.F) w.Completion
  let Λ : w.Completion ⊗[D.host.F] D.host.E →ₗ[w.Completion] w.Completion :=
    (TensorProduct.AlgebraTensorModule.rid D.host.F w.Completion w.Completion).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.map LinearMap.id φ
  have hΛ1 : ∀ e : D.host.E, Λ (ι e) = algebraMap D.host.F w.Completion (φ e) := by
    intro e
    simp [Λ, ι, inclR, Algebra.algebraMap_eq_smul_one]
  have : IsModuleTopology w.Completion (w.Completion ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (w.Completion ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing w.Completion _
  have hΛ : Continuous Λ := IsModuleTopology.continuous_of_linearMap Λ
  let f : GArch D.sp.cm.sig V.gram w → w.Completion := fun h =>
    Λ (((matHom _ D.sp.cm.sig V.gram h).val *ᵥ (fun i => ι (c i))) j)
  have hm : Continuous fun h : GArch D.sp.cm.sig V.gram w =>
      (matHom _ D.sp.cm.sig V.gram h).val :=
    Units.continuous_val.comp (isEmbedding_matHom _ _ _).continuous
  have hf : Continuous f := hΛ.comp ((continuous_apply j).comp (hm.matrix_mulVec continuous_const))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have he : ∀ γ : GF V, (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w γ)).val = (γ.1.1).map ι :=
    fun γ => rfl
  have hval : ∀ n : ℕ, f (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V)) =
      algebraMap D.host.F w.Completion ((2 : D.host.F) ^ n * φ (c j)) := by
    intro n
    have e1 : (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V))).val = ((g ^ n).1.1).map ι := he (g ^ n)
    simp only [f]
    rw [e1, show (fun i => ι (c i)) = ⇑ι ∘ c from rfl, ← RingHom.map_mulVec, hMn n, Pi.smul_apply, smul_eq_mul, hΛ1]
    congr 1
    rw [show (2 : D.host.E) ^ n * c j = ((2 : D.host.F) ^ n) • c j by rw [Algebra.smul_def, map_pow, map_ofNat],
      map_smul, smul_eq_mul]
  have hnorm : ∀ a : D.host.F, ‖algebraMap D.host.F w.Completion a‖ = w a := fun a => by
    rw [show algebraMap D.host.F w.Completion a = ((a : D.host.F) : w.Completion) from by
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply]]
    exact AbsoluteValue.Completion.norm_coe _
  have hpos : 0 < w (φ (c j)) := (InfinitePlace.pos_iff).2 hφ
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / w (φ (c j))) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun hmem => ?_⟩
  rw [show projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) = ratArch D.sp.cm.sig V.gram w (g ^ n : GF V) from
    projArch_ratEmb _ _ w _] at hmem
  have h1 := hC _ hmem
  rw [hval, hnorm, map_mul, map_pow] at h1
  have h2 : w (2 : D.host.F) = 2 := by
    rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
  rw [h2] at h1
  rw [div_lt_iff₀ hpos] at hn
  linarith

end GlobalTheory.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterTrivialBoundUnramifiedUnita
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LFun.SatCompare in
theorem GlobalTheory.Twist.satParam_exists_trivialBound : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KU σ n) → (∀ h ∈ Hecke ℂ (KU σ n), ∃ c : ℂ, heckeVec ρ (KU σ n) h x = c • x) → ∃ α, IsSatVecU ϖ q ρ x α ∧ GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ hρ x hx0 hxK hxH
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU
  obtain ⟨U, hU', hxU, hirr, hun, hline⟩ :=
    _root_.GlobalTheory.spherical_eigenvector_generates_irreducible ρ (KU σ n) ho (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n) hρ x hx0 hxK hxH
  set π := GlobalTheory.PRep.sub ρ U hU'
  set x' : U := ⟨x, hxU⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hx'K : x' ∈ fixed π (KU σ n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hxK k hk)
  have hs : GlobalTheory.LGrp.IsSpherical π (KU σ n) := (Submodule.ne_bot_iff _).2 ⟨x', hx'K, hx'0⟩
  have hf : FiniteDimensional ℂ (fixed π (KU σ n)) := by
    have hle : fixed π (KU σ n) ≤ Submodule.span ℂ {x'} := fun y hy => by
      obtain ⟨c, rfl⟩ := hline y hy
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
    exact Submodule.finiteDimensional_of_le hle
  obtain ⟨α, hα⟩ := exists_hasSatU hU hirr hf hs
  refine ⟨α, ?_, _root_.GlobalTheory.SatBoundInert.satakeBoundInert L ϖ σ q n hU U π α hirr hun hα⟩
  have := (hα.2 x' hx'K hx'0).map hU U.subtype (fun g y => rfl) hx0
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentSelf
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.FinLocSelf

theorem prV_swap_sndA {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (x : AF D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v (Formalism.IndefR.Lev.swapAE D
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) x)) =
    Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E (compFin D.host.F D.host.E v x) := by
  have h : ((Algebra.TensorProduct.map (AlgHom.id D.host.F D.host.E) (Formalism.UG.evalV D.host.F v)).comp
      ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).toAlgHom.comp
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)))) =
      (Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E).toAlgHom.comp
        (Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E)) :=
    Algebra.TensorProduct.ext' fun _ _ => rfl
  exact DFunLike.congr_fun h x

theorem finE_locFin_map_prV {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : Gv V v) :
    (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) v) =
      (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).val.map
        (Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E) := by
  conv_rhs => rw [← proj_emb_self D.sp.cm.sig V.gram v g]
  rw [matHom_proj]
  ext i j
  exact prV_swap_sndA v _

end GlobalTheory.FinLocSelf
end

