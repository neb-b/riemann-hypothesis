module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureHermitianModelOfDatum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Matrix in
theorem negIndex_transpose_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : GlobalTheory.Inertia.negIndex Jᵀ = q ∧ J.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  have hd : Formalism.UG.Jpq p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    rw [← fromBlocks_diagonal, Formalism.UG.Jpq]
    congr 1
    rw [← diagonal_neg]
    rfl
  have hPd : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det ≠ 0 := P.det_ne_zero
  constructor
  · have ht := congrArg Matrix.transpose hP
    rw [hd, diagonal_transpose, transpose_mul, transpose_mul, Formalism.UG.cT, transpose_transpose,
      ← Matrix.mul_assoc] at ht
    have h1 := GlobalTheory.Inertia.negIndex_eq_card_of_congr_diagonal hPd ht
    have h2 : (J.reindex e e)ᵀ = Jᵀ.submatrix e.symm e.symm := rfl
    rw [h2, GlobalTheory.Inertia.negIndex_submatrix_equiv] at h1
    rw [h1, Finset.card_filter, Fintype.sum_sum_type]
    simp [not_lt.2 (zero_le_one' ℝ)]
  · intro h0
    have h1 := congrArg Matrix.det hP
    rw [det_mul, det_mul, det_reindex_self, h0, hd, det_diagonal] at h1
    simp only [mul_zero, zero_mul] at h1
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h1.symm
    rcases k with k | k <;> simp

variable {D : D7}

theorem cc_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (a b : Fin r) :
    cc (gmW V hr a b) = gmW V hr b a := by
  subst hr
  show IsCMField.complexConj D.host.E (-(V.hT (V.frame b) (V.frame a))) = -(V.hT (V.frame a) (V.frame b))
  rw [map_neg]
  exact congrArg Neg.neg (LinearMap.isSymm_def.1 V.herm (V.frame b) (V.frame a))

theorem herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm) =
      -V.hT y x := by
  subst hr
  rw [Formalism.L2.Pj.DatLin.sesq_repr V.hT V.frame y x, Finset.sum_comm, herm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show V.frame.repr x a * (-(V.hT (V.frame b) (V.frame a))) * star (V.frame.repr y b) = _
  ring

theorem trace_herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    Algebra.trace ℚ D.host.E (D.host.xi0 *
      herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm)) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT x y) := by
  rw [herm_gmW, ← Formalism.L2.Pj.trace_cc D (D.host.xi0 * V.hT x y), map_mul (IsCMField.complexConj D.host.E), conj_xi0_alt]
  have h : IsCMField.complexConj D.host.E (V.hT x y) = V.hT y x := LinearMap.isSymm_def.1 V.herm x y
  rw [h, mul_neg, neg_mul]

theorem posIndex_gmW (V : HSp D) (hV : V.SigOK) {r : ℕ} (hr : V.rank = r) (τ : D.host.E →+* ℂ) :
    GlobalTheory.Inertia.posIndex ((gmW V hr).map τ) = (V.sig τ).2 ∧ (gmW V hr).det ≠ 0 := by
  subst hr
  obtain ⟨h1, h2⟩ := negIndex_transpose_of_hasSignature (hV τ)
  have e : gmW V rfl = -V.gram.transpose := rfl
  constructor
  · rw [← h1, ← GlobalTheory.Inertia.posIndex_neg, e]
    congr 1
    ext a b
    simp
  · rw [e, Matrix.det_neg, Matrix.det_transpose]
    refine mul_ne_zero (pow_ne_zero _ (by simp)) fun h0 => h2 ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

end GlobalTheory.RecDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.RatElt

theorem hform_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) :
    Formalism.UG.hform σ J (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ g * J * g) x y := by
  have h : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i; exact RingHom.map_mulVec σ g x i
  rw [hform_eq, hform_eq, h, Formalism.UG.cT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (σ ∘ x) (g.map σ)ᵀ, Matrix.vecMul_transpose]

theorem hform_single {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Formalism.UG.hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have h : σ ∘ (Pi.single i 1 : Fin n → A) = Pi.single i 1 := by
    funext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  rw [hform_eq, h]; simp

theorem mem_UJ_iff {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (g : GL (Fin n) A) :
    g ∈ Formalism.UG.UJ σ J ↔ ∀ x y, Formalism.UG.hform σ J ((g : Matrix (Fin n) (Fin n) A) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) A) *ᵥ y) = Formalism.UG.hform σ J x y := by
  change Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J ↔ _
  constructor
  · intro h x y; rw [hform_mulVec, h]
  · intro h; ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_mulVec, hform_single, hform_single] at this

theorem bc_mem_HR_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) E) :
    Formalism.UG.bc (inclR (F := F) R) g ∈ HR R σ J ↔ g ∈ Formalism.UG.UJ (σ : E →+* E) J := by
  have hinj : Function.Injective (inclR (F := F) (E := E) R) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective
  have hc : Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) =
      (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E)).map (inclR (F := F) R) := by
    ext i j; simp [Formalism.UG.cT, sigR, inclR]
  change Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) * J.map (inclR (F := F) R) *
      (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R) = J.map (inclR (F := F) R) ↔
    Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * J * (g : Matrix (Fin n) (Fin n) E) = J
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective hinj).eq_iff

theorem bc_map_incl {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
    [CommRing S] [Algebra F S] (φ : R →ₐ[F] S) {n : ℕ} (g : GL (Fin n) E) :
    (Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom (Formalism.UG.bc (inclR (F := F) R) g)).1 =
      (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) S) := by
  ext i j
  simp [Formalism.UG.bc, inclR]

variable {D : D7}

theorem herm_eq (V : HSp D) (x y : Fin V.rank → D.host.E) :
    herm (-V.gramᵀ) x y = - Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram y x := by
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  change x b * (-V.gram a b) * cc (y a) = -(cc (y a) * V.gram a b * x b)
  ring

theorem herm_iff (V : HSp D) (g : GL (Fin V.rank) D.host.E) :
    (∀ u v, herm (-V.gramᵀ) ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u)
      ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) ↔
    Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  rw [bc_mem_HR_iff, mem_UJ_iff]
  simp only [herm_eq, neg_inj]
  exact forall_comm

theorem fin_eq {V : HSp D} {γ : GA D V} {γ' : GL (Fin V.rank) D.host.E} (h : IsRat V γ γ') :
    (finHom V γ).1 = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Af D.host.F)) := by
  unfold finHom IsRat at *
  rw [MonoidHom.comp_apply, h]
  exact bc_map_incl _ _

theorem inf_eq {V : HSp D} {γ : GA D V} {γ' : GL (Fin V.rank) D.host.E} (h : IsRat V γ γ') :
    (infHom V γ).1 = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Ainf D.host.F)) := by
  unfold infHom IsRat at *
  rw [MonoidHom.comp_apply, h]
  exact bc_map_incl _ _

theorem rational_elements : ∀ (D : D7) (V : HSp D), (∀ γ, γ ∈ GQ V ↔ ∃ γ', IsRat V γ γ') ∧ (∀ γ γ', IsRat V γ γ' → (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v)) ∧ (∀ γ' : GL (Fin V.rank) D.host.E, (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) → ∃ γ, IsRat V γ γ') ∧ (∀ γ γ' δ δ', IsRat V γ γ' → IsRat V δ δ' → IsRat V (γ * δ) (γ' * δ') ∧ IsRat V γ⁻¹ γ'⁻¹) ∧ ∀ γ γ', IsRat V γ γ' → (∀ v, (finHom V γ).1 *ᵥ finVec V v = finVec V ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)) ∧ ∀ τ θ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → archM V θ γ = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ := by
  intro D V
  have hmem : ∀ γ γ', IsRat V γ γ' → Formalism.UG.bc (incA D) γ' ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    intro γ γ' h
    rw [← h]; exact γ.2
  have : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  refine ⟨fun γ => ⟨?_, ?_⟩, fun γ γ' h => (herm_iff V γ').2 (hmem γ γ' h),
    fun γ' h => ⟨⟨_, (herm_iff V γ').1 h⟩, rfl⟩, fun γ γ' δ δ' h k => ⟨?_, ?_⟩, fun γ γ' h => ⟨fun v => ?_, fun τ θ hθ => ?_⟩⟩
  · rintro ⟨γ', -, h⟩
    exact ⟨γ', h.symm⟩
  · rintro ⟨γ', h⟩
    exact ⟨γ', (bc_mem_HR_iff _ _ _ _).1 (hmem γ γ' h), h.symm⟩
  · unfold IsRat at *
    rw [map_mul, map_mul, h, k]
  · unfold IsRat at *
    rw [map_inv, map_inv, h]
  · rw [fin_eq h]
    funext i
    exact (RingHom.map_mulVec (inclR (F := D.host.F) (Af D.host.F))
      (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) v i).symm
  · unfold archM
    rw [inf_eq h]
    ext i j
    exact hθ.1 _

end GlobalTheory.Member.RatElt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReFrameIffReframeIntegral
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ReframeClauses

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.L2.PjFree (FrBaseChg ReFrame XoNumPt TanLin SClause IntRebase)

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

end Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

section Comb

variable {S S' : Type} [CommRing S] [CommRing S']

theorem isTanAt_of_isCombAt {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v a w) : IsTanAt x w := by
  rw [← (ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_isComb_iff x v hv a w).1 h]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_comb_tan x _ (fun j => hv j) a

theorem isEigAt_of_isCombAt [Algebra c.F S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) {τ : E →+* ℂ}
    (he : ∀ j, IsEigAt c τ (v j)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v a w) : IsEigAt c τ w := by
  rw [← (ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_isComb_iff x v hv a w).1 h]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_comb_eig x c τ (fun j => ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_lt x (v j) (hv j)) he a

end Comb

section Gen

variable {S : Type} [CommRing S] [Algebra c.F S]

end Gen

variable (Xo c)

variable {Xo c}

end GlobalTheory.ReframeClauses
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem univFrame_classifies : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (z : FrPt Xo c T) (ψ : R →ₐ[c.F] T), z.x = spMap ψ.toRingHom ≫ y₀.x → ∃! a : A →ₐ[c.F] T, a.comp π = ψ ∧ FrMap a u z := by
  intro hS E _ _ _ H Dw l Xo c R _ _ A _ _ y₀ π X s u hu T _ _ z ψ hz
  obtain ⟨⟨-, hring⟩, u₀, hu₀, hchg⟩ := hu
  obtain ⟨z₀, hz₀⟩ := _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c R T ψ y₀
  have hx₀ : z₀.x = spMap ψ.toRingHom ≫ y₀.x :=
    (((_root_.GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c R T ψ y₀).2.2 z₀).1 hz₀).1
  obtain ⟨hex, huniq⟩ := _root_.GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c T z₀ z
  obtain ⟨g, a₀, hg, hgz⟩ := hex (hz.trans hx₀.symm)
  have key : ∀ k : A →ₐ[c.F] T, k.comp π = ψ →
      (FrMap k u z ↔ FrChg (fun τ => (X τ).map k) (k (s : A)) z₀ z) := by
    intro k hk
    obtain ⟨w, hw⟩ := _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c A T k u₀
    have hw' : FrMap (k.comp π) y₀ w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y₀ u₀ w hu₀ hw
    rw [hk] at hw'
    obtain rfl : w = z₀ := (_root_.GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c R T ψ y₀).1 w z₀ hw' hz₀
    exact _root_.GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A T k u₀ u w z X (s : A) hchg hw
  obtain ⟨k, ⟨hk, hkX, hks⟩, hku⟩ := hring T ψ g a₀ hg
  refine ⟨k, ⟨hk, (key k hk).2 ?_⟩, ?_⟩
  · have h1 : (fun τ => (X τ).map k) = g := funext hkX
    rw [h1, hks]
    exact hgz
  · rintro k' ⟨hk', hm⟩
    obtain ⟨h1, h2⟩ := huniq _ _ _ _ ((key k' hk').1 hm) hgz
    exact hku k' ⟨hk', fun τ => congrFun h1 τ, h2⟩

end GlobalTheory.Frames
end

