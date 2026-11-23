module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeTrans

section Abstract

variable {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem mulVec_mem (S : Subring R) (u : Matrix m m S) (x : m → R) (hx : ∀ i, x i ∈ S) (i : m) :
    (u.map S.subtype).mulVec x i ∈ S := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact S.sum_mem fun k _ => S.mul_mem (u i k).2 (hx k)

theorem frame_inv (S : Subring R) (β : GL n R) (β' : GL m R) (c : n ≃ m) (U : GL m R) (u u' : Matrix m m S)
    (hu : U.val = u.map S.subtype) (hu' : (U⁻¹).val = u'.map S.subtype) (j : Matrix m n R)
    (hj : j * β.val = (β' * U).val.submatrix id c) :
    (∃ j' : Matrix n m R, j * j' = 1 ∧ j' * j = 1) ∧
      ∀ x : n → R, (∀ i, (β⁻¹).val.mulVec x i ∈ S) ↔ ∀ i, (β'⁻¹).val.mulVec (j.mulVec x) i ∈ S := by
  have hj2 : j = (β' * U).val.submatrix id c * (β⁻¹).val := by
    rw [← hj, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨⟨β.val * ((β' * U)⁻¹).val.submatrix c id, ?_, ?_⟩, fun x => ?_⟩
  · rw [← Matrix.mul_assoc, hj, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_id_id]
  · have h1 : ((β' * U)⁻¹).val.submatrix c id * (β' * U).val.submatrix id c = 1 := by
      have := Matrix.submatrix_mul_equiv ((β' * U)⁻¹).val (β' * U).val c (Equiv.refl m) c
      rw [Units.inv_mul, Matrix.submatrix_one_equiv] at this
      exact this
    rw [hj2, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.submatrix _ _ _), h1, Matrix.one_mul, Units.mul_inv]
  · have h1 : j.mulVec x = (β' * U).val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [hj2, ← Matrix.mulVec_mulVec, Matrix.submatrix_mulVec_equiv]
      rfl
    have h2 : (β'⁻¹).val.mulVec (j.mulVec x) = U.val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [h1, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [h2]
    constructor
    · intro h i
      rw [hu]
      exact mulVec_mem S u _ (fun k => h _) i
    · intro h i
      have h3 := mulVec_mem S u' _ h (c i)
      rw [← hu', Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Function.comp_apply, Equiv.symm_apply_apply] at h3
      exact h3

variable {f : R} {J : Matrix m n R} {J' : Matrix n m R} {M : Matrix n n R} {M' : Matrix m m R}

omit [DecidableEq n] in
theorem conj_eq (h1 : J * J' = 1) (hc : M' * J = J * M) : M' = J * M * J' := by
  rw [← hc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conj_inv (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M * J' = J' * M' := by
  rw [conj_eq h1 hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem supp_conj (h1 : J * J' = 1) (hc : M' * J = J * M) (hs : f • (M - 1) = M - 1) : f • (M' - 1) = M' - 1 := by
  have hs2 : M' - 1 = J * (M - 1) * J' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, ← conj_eq h1 hc]
  rw [hs2, ← Matrix.smul_mul, ← Matrix.mul_smul, hs]

theorem det_conj (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M'.det = M.det := by
  rw [conj_eq h1 hc]
  exact Matrix.det_conj_of_mul_eq_one h1 h2

variable {L : AddSubgroup (n → R)} {L' : AddSubgroup (m → R)}

omit [DecidableEq n] in
theorem lat_inv (h1 : J * J' = 1) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L') (y : m → R) :
    f • y ∈ L' ↔ f • J'.mulVec y ∈ L := by
  rw [hL, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

omit [DecidableEq n] in
theorem stab_conj (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc' : ∀ y ∈ L', f • y ∈ L') (ha : ∀ y ∈ L, f • M.mulVec y ∈ L) : ∀ y ∈ L', f • M'.mulVec y ∈ L' := by
  intro y hy
  have h3 := ha _ ((lat_inv h1 hL y).1 (loc' y hy))
  rw [hL, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← conj_eq h1 hc] at h3
  exact h3

omit [DecidableEq n] in
theorem cont_conj {p : R} (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc : ∀ y ∈ L, f • y ∈ L) (loc' : ∀ y ∈ L', f • y ∈ L') (hb : ∀ y ∈ L, ∃ z ∈ L, f • p • y = f • M.mulVec z) :
    ∀ y ∈ L', ∃ z ∈ L', f • p • y = f • M'.mulVec z := by
  intro y hy
  obtain ⟨z, hz, h3⟩ := hb _ ((lat_inv h1 hL y).1 (loc' y hy))
  refine ⟨f • J.mulVec z, (hL z).1 (loc z hz), ?_⟩
  have h4 := congrArg J.mulVec h3
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1,
    Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hc, smul_comm p, smul_smul, hf] at h4
  rw [h4, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec]

variable {R' : Type} [CommRing R']

omit [Fintype n] in
theorem supp_map_iff (φ : R' →+* R) (g : R') (A : Matrix n n R') :
    φ g • (A.map φ - 1) = A.map φ - 1 ↔ ∀ i j, φ (g * (A - 1) i j) = φ ((A - 1) i j) := by
  have h : ∀ i j, φ ((A - 1) i j) = (A.map φ - 1) i j := by
    intro i j
    rw [← Matrix.map_one φ φ.map_zero φ.map_one]
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub]
  simp only [map_mul, h]
  rw [← Matrix.ext_iff]
  rfl

omit [DecidableEq m] in
theorem map_mul_one (φ : R' →+* R) {A : Matrix n m R'} {B : Matrix m n R'} (h : A * B = 1) : A.map φ * B.map φ = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ φ.map_zero φ.map_one]

omit [DecidableEq m] [DecidableEq n] in
theorem map_conj (φ : R' →+* R) {A : Matrix m m R'} {B : Matrix m n R'} {C : Matrix n n R'} (h : A * B = B * C) :
    A.map φ * B.map φ = B.map φ * C.map φ := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

omit [DecidableEq m] [DecidableEq n] [Fintype m] in
theorem mulVec_map_inv (φ : R' →+* R) (ψ : R →+* R') (h : ∀ x, ψ (φ x) = x) (j : Matrix m n R') (y : n → R) :
    (j.mulVec fun a => ψ (f * y a)) = fun a => ψ (f * (j.map φ).mulVec y a) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, h]
  exact Finset.sum_congr rfl fun b _ => mul_left_comm _ _ _

theorem map_mul_det (φ : R' →+* R) (e : R') (A : Matrix m m R') (B : Matrix n n R') (h : (A.map φ).det = (B.map φ).det) :
    φ (e * A.det) = φ (e * B.det) := by
  rw [map_mul, map_mul, RingHom.map_det, RingHom.map_det]
  exact congrArg (φ e * ·) h

end Abstract

variable {D : D7}

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (mt V g).map (finPart D) := rfl

theorem inf_eq {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) : (mt V g).map (infPart D) = 1 :=
  congrArg Units.val (MonoidHom.mem_ker.1 hg)

theorem idem_det {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {m n : ℕ} (A : Matrix (Fin m) (Fin m) (Formalism.L2.Theta.AE D))
    (B : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)) (h : (A.map (finPart D)).det = (B.map (finPart D)).det) :
    e * A.det = e * B.det := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ (map_mul_det (finPart D) e A B h)
  simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]

theorem suppAt_iff (e : Formalism.L2.Theta.AE D) {V : HSp D} {α : GA D V} (hα : α ∈ GfC V) :
    SuppAt e V α ↔ finPart D (e + cA D e) • (finMat D.sp.cm.sig V.gram α - 1) = finMat D.sp.cm.sig V.gram α - 1 := by
  rw [finMat_eq, supp_map_iff]
  refine ⟨fun hs i j => congrArg (finPart D) (hs i j), fun hs i j => ?_⟩
  have hs4 := (supp_map_iff (infPart D) (e + cA D e) (mt V α)).1 (by rw [inf_eq hα, sub_self, smul_zero])
  exact GlobalTheory.SplitScalar.adele_ext (hs4 i j) (hs i j)

theorem transfer {V V' : HSp D} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e)
    (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (h1 : HMul.hMul J J' = 1) (h2 : HMul.hMul J' J = 1) {α : GA D V} {α' : GA D V'} (hα' : α' ∈ GfC V')
    (hc : HMul.hMul (finMat D.sp.cm.sig V'.gram α') J = HMul.hMul J (finMat D.sp.cm.sig V.gram α))
    (hL : ∀ y, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D e • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V')
    (loc : ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V)
    (loc' : ∀ y ∈ Formalism.L2.NTheta.LamHat V', finPart D e • y ∈ Formalism.L2.NTheta.LamHat V')
    {ϖ : D.host.E} {k : ℕ} (h : Formalism.L2.NTheta.IsHeckeElt V e ϖ k α) : Formalism.L2.NTheta.IsHeckeElt V' e ϖ k α' := by
  obtain ⟨hα, hs, ha, hb, u, u', hu, hu', huu, hd⟩ := h
  have hf : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he.1]
  refine ⟨hα', ?_, stab_conj hf h1 hc hL loc' ha, cont_conj hf h1 hc hL loc loc' hb, u, u', hu, hu', huu, ?_⟩
  · exact (suppAt_iff e hα').2 (supp_conj h1 hc ((suppAt_iff e hα).1 hs))
  · exact (idem_det he _ _ (det_conj h1 h2 hc)).trans hd

def unswap (D : D7) : EAf D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm.toAlgHom.toRingHom

theorem unswap_swap (x) : unswap D (swapAE D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm_apply_apply x

theorem swap_unswap (x) : swapAE D (unswap D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).apply_symm_apply x

theorem finE_unswap (V : HSp D) (g : GA D V) : (finE V g).val.map (unswap D) = finMat D.sp.cm.sig V.gram g := by
  ext i j
  exact unswap_swap _

end GlobalTheory.HeckeTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemGoodPart
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Bridge Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.HeckeModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Group

variable {G : Type} [Group G]

theorem sum_eq_of_isDC {J : Subgroup G} {x x' : G} {A A' : Finset G} {F : G → ℂ} (hA : IsDC J x A) (hA' : IsDC J x' A')
    (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) (hF : ∀ k ∈ J, ∀ h, F (h * k) = F h) (h : G) :
    ∑ a ∈ A, F (h * a) = ∑ a ∈ A', F (h * a) :=
  congrFun (GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x' A A' F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA' hx
    (fun k h => by simpa using hF k k.2 h)).1 h

theorem sum_inv_of_isDC {J : Subgroup G} {x : G} {A : Finset G} {F : G → ℂ} (hA : IsDC J x A)
    (hF : ∀ k ∈ J, ∀ h, F (h * k) = F h) (k : G) (hk : k ∈ J) (h : G) :
    ∑ a ∈ A, F (h * k * a) = ∑ a ∈ A, F (h * a) := by
  have := (GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x A A F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA ⟨1, 1, by simp⟩
    (fun k h => by simpa using hF k k.2 h)).2 ⟨k, hk⟩ h
  simpa [dcOp] using this

theorem mem_of_isDC {K L : Subgroup G} (hKL : K ≤ L) {x : G} (hx : x ∈ L) {A : Finset G} (hA : IsDC K x A) :
    ∀ a ∈ A, a ∈ L := by
  intro a ha
  obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
  exact L.mul_mem (L.mul_mem (hKL k₁.2) hx) (hKL k₂.2)

structure Splits (J K L : Subgroup G) : Prop where
  le : K ≤ L
  mem : ∀ g ∈ L, g ∈ J ↔ g ∈ K
  dec : ∀ k ∈ J, ∃ k₁ ∈ K, ∃ k₂ ∈ J, k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l

theorem Splits.le' {J K L : Subgroup G} (hs : Splits J K L) : K ≤ J := fun g hg => (hs.mem g (hs.le hg)).2 hg

theorem Splits.isDC {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G} (hA : IsDC K x A) :
    IsDC J x A := by
  have hAL := mem_of_isDC hs.le hx hA
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
    exact ⟨⟨k₁, hs.le' k₁.2⟩, ⟨k₂, hs.le' k₂.2⟩, rfl⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a₁, ha₁, b₁, hb₁, e₁, c₁⟩ := hs.dec k₁ k₁.2
    obtain ⟨a, ⟨ha, hak⟩, -⟩ := hA.2 (a₁ * x) ⟨⟨a₁, ha₁⟩, 1, by simp⟩
    have hmem : a⁻¹ * (k₁ * x * k₂) ∈ J := by
      have : a⁻¹ * ((k₁ : G) * x * k₂) = a⁻¹ * (a₁ * x) * (b₁ * k₂) := by
        rw [e₁, mul_assoc a₁ b₁ x, (c₁ x hx).eq]; group
      rw [this]
      exact J.mul_mem (hs.le' hak) (J.mul_mem hb₁ k₂.2)
    refine ⟨a, ⟨ha, hmem⟩, ?_⟩
    rintro a' ⟨ha', hmem'⟩
    have h1 : a⁻¹ * a' ∈ J := by
      have : a⁻¹ * a' = (a⁻¹ * ((k₁ : G) * x * k₂)) * (a'⁻¹ * (k₁ * x * k₂))⁻¹ := by group
      rw [this]; exact J.mul_mem hmem (J.inv_mem hmem')
    have h2 : a⁻¹ * a' ∈ K := (hs.mem _ (L.mul_mem (L.inv_mem (hAL a ha)) (hAL a' ha'))).1 h1
    exact (hA.2 a' (hA.1 a' ha')).unique ⟨ha', by simp [K.one_mem]⟩ ⟨ha, h2⟩

theorem Splits.sum_transl {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G}
    (hA : IsDC K x A) {F : G → ℂ} (hF : ∀ k ∈ K, ∀ h, F (h * k) = F h) {κ : G} (hκ : κ ∈ J) (h : G) :
    ∑ a ∈ A, F (h * κ * a) = ∑ a ∈ A, F (h * a * κ) := by
  have hAL := mem_of_isDC hs.le hx hA
  obtain ⟨a₁, ha₁, b₁, -, rfl, c₁⟩ := hs.dec κ hκ
  have e1 : a₁ * b₁ = b₁ * a₁ := (c₁ a₁ (hs.le ha₁)).eq.symm
  rw [e1, ← mul_assoc, sum_inv_of_isDC hA hF a₁ ha₁]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← mul_assoc, hF a₁ ha₁, mul_assoc, (c₁ a (hAL a ha)).eq, mul_assoc]

end Group

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

structure OffAt (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (K large₂ : Subgroup (GA D V)) : Prop where
  splits : Splits (levG V β L) K large₂
  chi : ∀ k ∈ K, levChi V β L k = 1

theorem inv_of_mem_mult {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)} (hL : OffAt β L K large₂) {T : MMap M}
    (hT : T ∈ Mult θ M (levS V β L) (levChi V β L)) (v : M.Vec) : ∀ k ∈ K, ∀ h, T v (h * k) = T v h := by
  intro k hk h
  rw [((GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT).lev v k (hL.splits.le' hk) h, hL.chi k hk, one_mul]

theorem heckeOn_mem_mult {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)} (hL : OffAt β L K large₂) (hf : large₂ ≤ GfC V)
    {x : GA D V} (hx : x ∈ large₂) {A : Finset (GA D V)} (hA : IsDC K x A) {T : MMap M}
    (hT : T ∈ Mult θ M (levS V β L) (levChi V β L)) : heckeOn M A T ∈ Mult θ M (levS V β L) (levChi V β L) := by
  classical
  have hAL := mem_of_isDC hL.splits.le hx hA
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT
  have h0 : IsMultMap θ M ∅ (levChi V β L) T := ⟨hT'.aut, hT'.cusp, fun _ _ hk => absurd hk (Set.notMem_empty _), hT'.equiv, hT'.cont⟩
  have hex : ∀ a : GA D V, ∃ T' : MMap M, a ∈ A → IsMultMap θ M ∅ (levChi V β L) T' ∧ ∀ v, T' v = rTr V a (T v) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨T', h⟩ := _root_.GlobalTheory.isMultMap_rightTranslate_finite θ M ∅ (levChi V β L) a (hf (hAL a ha))
        (fun k hk => absurd hk (Set.notMem_empty _)) T h0
      exact ⟨T', fun _ => h⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose Ta hTa using hex
  have e : heckeOn M A T = ∑ a ∈ A, Ta a := by
    ext v g
    rw [MultilinearMap.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a ha => (congrFun ((hTa a ha).2 v) g).symm
  have h1 : IsMultMap θ M ∅ (levChi V β L) (heckeOn M A T) := by
    rw [← GlobalTheory.MultMem.mem_mult_iff, e]
    exact Submodule.sum_mem _ fun a ha => Submodule.subset_span (hTa a ha).1
  refine Submodule.subset_span ⟨h1.aut, h1.cusp, fun v k hk g => ?_, h1.equiv, h1.cont⟩
  show ∑ a ∈ A, T v (g * k * a) = levChi V β L k * ∑ a ∈ A, T v (g * a)
  rw [hL.splits.sum_transl hx hA (inv_of_mem_mult hL hT v) hk, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => hT'.lev v k hk _

theorem heckeLin_actL {β : GL (Fin V.rank) (Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)}
    (hL : OffAt β (flagL L) K large₂) {x : GA D V} (hx : x ∈ large₂) {A : Finset (GA D V)} (hA : IsDC K x A)
    {F : GA D V → ℂ} (hF : ∀ k ∈ K, ∀ h, F (h * k) = F h) (g0 : Formalism.L2.DIV.G0 L.Pg L.r) :
    actL V β L g0 (heckeLin V A F) = heckeLin V A (actL V β L g0 F) := by
  funext h
  show actG0 V β L g0 (heckeLin V A F) h = ∑ a ∈ A, actG0 V β L g0 F (h * a)
  unfold actG0
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  · simp only [dif_pos hk]
    have hκ : hk.choose ∈ levG V β (flagL L) := ⟨hk.choose_spec.1, hk.choose_spec.2.1, Subgroup.mem_top _⟩
    rw [heckeLin_apply, hL.splits.sum_transl hx hA hF hκ, Finset.mul_sum]
  · simp [dif_neg hk]

theorem offAt_of_place {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hβ : IsBaseFrame V β Λ N) {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    (hL : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P) {K large₂ : Subgroup (GA D V)}
    (hLg : ∀ g, g ∈ large₂ ↔ SuppAt e V g) (hK : ∀ g, g ∈ K ↔ g ∈ locPart V (KsphC V ∅) e) : OffAt β L K large₂ := by
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N L hβ).2 P e _ hp hN hL
  obtain ⟨hf, hcf, -⟩ := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e _ hp
  have hc := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).1 _ hf hcf).2.2
  refine ⟨⟨fun g hg => (hLg g).2 ((hK g).1 hg).2, fun g hg => ?_, fun k hk => ?_⟩, fun k hk => ?_⟩
  · rw [h1 g ((hLg g).1 hg), hK]
    exact ⟨fun h => ⟨h, (hLg g).1 hg⟩, fun h => h.1⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, s₁, s₂, rfl⟩ := h3 k hk
    refine ⟨k₁, (hK _).2 ⟨(h1 _ s₁).1 hk₁, s₁⟩, k₂, hk₂, rfl, fun l hl => ?_⟩
    exact (hc (1 - (e + cA D e)) l k₂ (by rw [mul_sub, mul_one, hf, sub_self]) ((hLg l).1 hl) s₂).symm
  · have := (hK k).1 hk
    exact h2 k ((h1 k this.2).2 this.1) this.2

end GlobalTheory.HeckeModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.SignatureOneForms

theorem form_re_eq_sum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (v : Fin n → ℂ) :
    (star v ⬝ᵥ A *ᵥ v).re = ∑ i, hA.eigenvalues i *
      Complex.normSq ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℂ := RCLike.ofReal ∘ hA.eigenvalues with hd
  set c := star U *ᵥ v with hc
  have hspec : A = U * diagonal d * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hU, hd]
  have h0 := congrArg (fun M => star v ⬝ᵥ M *ᵥ v) hspec
  have h1 : star v ⬝ᵥ A *ᵥ v = star c ⬝ᵥ (diagonal d *ᵥ c) := by
    rw [h0, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hc, star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  rw [h1]
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, hd, Function.comp_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem form_re_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hdet : A.det ≠ 0)
    (i₀ : Fin n) (hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀) (v : Fin n → ℂ) (hv : v ≠ 0)
    (hv0 : (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i₀ = 0) :
    (star v ⬝ᵥ A *ᵥ v).re < 0 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set c := star U *ᵥ v with hc
  have hne : ∀ i, hA.eigenvalues i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hcne : c ≠ 0 := by
    intro h0
    apply hv
    have : U *ᵥ c = v := by
      rw [hc, mulVec_mulVec, hU, Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, one_mulVec]
    rw [← this, h0, mulVec_zero]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hcne
  have hji : j ≠ i₀ := by
    rintro rfl
    exact hj hv0
  have hjneg : hA.eigenvalues j < 0 :=
    lt_of_le_of_ne (not_lt.mp fun h => hji (hpos j h)) (hne j)
  rw [form_re_eq_sum hA v]
  have key : ∑ i, hA.eigenvalues i * Complex.normSq (c i) < ∑ _i : Fin n, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i = i₀
      · subst hi
        simp [hv0]
      · have : hA.eigenvalues i ≤ 0 := not_lt.mp fun h => hi (hpos i h)
        nlinarith [Complex.normSq_nonneg (c i)]
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      exact mul_neg_of_neg_of_pos hjneg (Complex.normSq_pos.mpr hj)
  simpa using key

end GlobalTheory.SignatureOneForms

namespace GlobalTheory

theorem re_form_neg_of_orth_of_sigPosH_eq_one : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 1 → ∀ x y : Fin n → ℂ, 0 < (star x ⬝ᵥ A *ᵥ x).re → star x ⬝ᵥ A *ᵥ y = 0 → y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  intro n A hA hdet hsig x y hx hxy hy
  unfold sigPosH at hsig
  obtain ⟨⟨i₀, hi₀⟩, huniq⟩ := Fintype.card_eq_one_iff.mp hsig
  have hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀ := fun i h => congrArg Subtype.val (huniq ⟨i, h⟩)
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hyx : star y ⬝ᵥ A *ᵥ x = 0 := by
    have h := congrArg star hxy
    rw [star_zero] at h
    rw [← h, star_dotProduct, star_mulVec, hA.eq, ← dotProduct_mulVec]
  by_contra hQ
  push_neg at hQ
  set a₀ := (star U *ᵥ x) i₀ with ha₀
  set b₀ := (star U *ᵥ y) i₀ with hb₀
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  by_cases ha : a₀ = 0
  · exact absurd (GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos x hx0 ha) (not_lt.mpr hx.le)
  set w := b₀ • x - a₀ • y with hw
  have hw0 : (star U *ᵥ w) i₀ = 0 := by
    simp only [hw, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← ha₀, ← hb₀]
    ring
  have hQw : star w ⬝ᵥ A *ᵥ w = (Complex.normSq b₀ : ℂ) * (star x ⬝ᵥ A *ᵥ x)
      + (Complex.normSq a₀ : ℂ) * (star y ⬝ᵥ A *ᵥ y) := by
    simp only [hw, star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, hxy, hyx, smul_eq_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  by_cases hw' : w = 0
  · have h1 : star x ⬝ᵥ A *ᵥ w = b₀ * (star x ⬝ᵥ A *ᵥ x) := by
      simp [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hxy]
    rw [hw', mulVec_zero, dotProduct_zero] at h1
    have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hx; simp at hx
    have hb : b₀ = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hQx
    have : a₀ • y = 0 := by
      have hw2 : b₀ • x - a₀ • y = 0 := hw ▸ hw'
      rw [hb, zero_smul, zero_sub, neg_eq_zero] at hw2
      exact hw2
    exact hy ((smul_eq_zero.mp this).resolve_left ha)
  · have hneg := GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos w hw' hw0
    rw [hQw, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hneg
    nlinarith [Complex.normSq_nonneg a₀, Complex.normSq_nonneg b₀,
      mul_nonneg (Complex.normSq_nonneg b₀) hx.le, mul_nonneg (Complex.normSq_nonneg a₀) hQ]

end GlobalTheory
end

