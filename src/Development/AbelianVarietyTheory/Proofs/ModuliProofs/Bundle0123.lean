module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerIntegerMatrixPrimitiveAdjoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PowerAdjoint

open GlobalTheory.CechPic

section Algebra

variable {M : Type} {V : Type 1} [AddCommGroup M] [AddCommGroup V] {n : Type} [Fintype n]

def form (B : M →+ M →+ V) (W : Matrix n n ℤ) (x y : n → M) : V := ∑ u, ∑ v, W u v • B (x u) (y v)

theorem form_left (B : M →+ M →+ V) (W m : Matrix n n ℤ) (x y : n → M) :
    form B W (fun u => ∑ v, m u v • x v) y = form B (m.transpose * W) x y := by
  have hL : form B W (fun u => ∑ v, m u v • x v) y = ∑ u, ∑ v, ∑ w, (W u v * m u w) • B (x w) (y v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [form, Finset.smul_sum, smul_smul, map_sum]
  have hR : form B (m.transpose * W) x y = ∑ w, ∑ v, ∑ u, (m u w * W u v) • B (x w) (y v) := by
    simp [form, Matrix.mul_apply, Finset.sum_smul]
  rw [hL, hR]
  calc ∑ u, ∑ v, ∑ w, (W u v * m u w) • B (x w) (y v)
      = ∑ u, ∑ w, ∑ v, (W u v * m u w) • B (x w) (y v) := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ w, ∑ u, ∑ v, (W u v * m u w) • B (x w) (y v) := Finset.sum_comm
    _ = ∑ w, ∑ v, ∑ u, (m u w * W u v) • B (x w) (y v) := Finset.sum_congr rfl fun _ _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem form_right (B : M →+ M →+ V) (W m : Matrix n n ℤ) (x y : n → M) :
    form B W x (fun u => ∑ v, m u v • y v) = form B (W * m) x y := by
  have hL : form B W x (fun u => ∑ v, m u v • y v) = ∑ u, ∑ v, ∑ w, (W u v * m v w) • B (x u) (y w) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [form, Finset.smul_sum, smul_smul, map_sum]
  have hR : form B (W * m) x y = ∑ u, ∑ w, ∑ v, (W u v * m v w) • B (x u) (y w) := by
    simp [form, Matrix.mul_apply, Finset.sum_smul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem form_polar (B : M →+ M →+ V) (hB : ∀ a b, B a b = B b a) (W : Matrix n n ℤ) (x y : n → M) :
    form B W (x + y) (x + y) - form B W x x - form B W y y + form B W 0 0 = form B (W + W.transpose) x y := by
  have hyx : ∑ u, ∑ v, W u v • B (y u) (x v) = ∑ u, ∑ v, W v u • B (x u) (y v) := by
    rw [Finset.sum_comm]
    simp only [hB (y _) (x _)]
  simp only [form, Pi.add_apply, Pi.zero_apply, map_add (f := _), map_zero, AddMonoidHom.add_apply,
    smul_add, smul_zero, Finset.sum_add_distrib, Finset.sum_const_zero, Matrix.add_apply, Matrix.transpose_apply, add_smul]
  rw [hyx]
  abel

end Algebra

section Square

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]


omit [IsCommMonObj B] in
theorem exists_biadditive {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (T : Over S) (hb : ∀ x x' y : T ⟶ B, ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen) :
    ∃ β : Additive (T ⟶ B) →+ Additive (T ⟶ B) →+ Pic T.left, (∀ a b, β a b = β b a) ∧
      ∀ x y : T ⟶ B, β (.ofMul x) (.ofMul y) = pull (lift x y).left (cls P hP) := by
  have add1 : ∀ x x' y : T ⟶ B, pull (lift (x * x') y).left (cls P hP) =
      pull (lift x y).left (cls P hP) + pull (lift x' y).left (cls P hP) := by
    intro x x' y
    have h0 := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hb x x' y)
    rw [cls_linComb hP] at h0
    simp [Fin.sum_univ_three] at h0
    rw [← sub_eq_zero, ← h0]
    abel
  have e1 : cls P hP = pull (lift (snd B B) (fst B B)).left (cls P hP) := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP _).2 hs
  have hsym : ∀ x y : T ⟶ B, pull (lift y x).left (cls P hP) = pull (lift x y).left (cls P hP) := by
    intro x y
    have e2 : (lift y x).left ≫ (lift (snd B B) (fst B B)).left = (lift x y).left := by
      rw [← Over.comp_left]
      congr 1
      ext <;> simp
    calc pull (lift y x).left (cls P hP)
        = pull (lift y x).left (pull (lift (snd B B) (fst B B)).left (cls P hP)) := by rw [← e1]
      _ = pull (lift x y).left (cls P hP) := by rw [← pull_comp, e2]
  have add2 : ∀ x y y' : T ⟶ B, pull (lift x (y * y')).left (cls P hP) =
      pull (lift x y).left (cls P hP) + pull (lift x y').left (cls P hP) := by
    intro x y y'
    rw [hsym (y * y') x, add1, ← hsym y x, ← hsym y' x]
  refine ⟨AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => pull (lift a.toMul b.toMul).left (cls P hP))
    fun b b' => ?_) fun a a' => ?_, fun a b => ?_, fun x y => rfl⟩
  · rw [toMul_add]
    exact add2 _ _ _
  · ext b
    simp only [toMul_add]
    exact add1 _ _ _
  · exact (hsym a.toMul b.toMul).symm

theorem comp_prod_zpow {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ B)) (k : Fin n → ℤ) :
    ρ ≫ (List.ofFn fun v => x v ^ k v).prod = (List.ofFn fun v => (ρ ≫ x v) ^ k v).prod := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => simp [List.ofFn_succ, MonObj.comp_mul, GrpObj.comp_zpow, ih]

theorem ofMul_comp_matrix {Q T : Over S} {n : ℕ} (pr : Fin n → (Q ⟶ B)) (m : Matrix (Fin n) (Fin n) ℤ) (α : Q ⟶ Q)
    (hα : ∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) (x : T ⟶ Q) :
    (fun u => Additive.ofMul ((x ≫ α) ≫ pr u)) = fun u => ∑ v, m u v • Additive.ofMul (x ≫ pr v) := by
  funext u
  rw [Category.assoc, hα u, comp_prod_zpow]
  simp [ofMul_list_prod, List.sum_ofFn, ofMul_zpow]

theorem exists_form {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (T : Over S) (hb : ∀ x x' y : T ⟶ B, ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen)
    {Q : Over S} [GrpObj Q] [IsCommMonObj Q] {n : Type} [Fintype n] (pr : n → (Q ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    {L : LB Q.left} (hL : L.IsLB) (W : Matrix n n ℤ)
    (hW : LBIso L (LB.LinComb P (K := n × n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2))) :
    ∃ β : Additive (T ⟶ B) →+ Additive (T ⟶ B) →+ Pic T.left,
      (∀ x : T ⟶ Q, pull x.left (cls L hL) =
        form β W (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (x ≫ pr u))) ∧
      ∀ (x y : T ⟶ Q) hh, cls (cubeLB Q ![x, y] L) hh =
        form β (W + W.transpose) (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (y ≫ pr u)) := by
  obtain ⟨β, hβs, hβ⟩ := exists_biadditive hP hs T hb
  have hpt : ∀ x : T ⟶ Q, pull x.left (cls L hL) =
      form β W (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (x ≫ pr u)) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hW, cls_linComb hP, map_sum, Fintype.sum_prod_type]
    simp only [form]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hβ]
  refine ⟨β, hpt, fun x y hh => ?_⟩
  have hxy : (fun u => Additive.ofMul ((x * y) ≫ pr u)) =
      (fun u => Additive.ofMul (x ≫ pr u)) + fun u => Additive.ofMul (y ≫ pr u) := by
    funext u
    have := hpr u
    simp [MonObj.mul_comp]
  have h1 : (fun u => Additive.ofMul ((1 : T ⟶ Q) ≫ pr u)) = 0 := by
    funext u
    have := hpr u
    simp [MonObj.one_comp]
  rw [cls_cube_two hL x y hh, lam, hpt, hpt, hpt, hpt, hxy, h1]
  exact form_polar β hβs W _ _

theorem primitive_adjoint {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (hb : ∀ (T : Over S) (x x' y : T ⟶ B), ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen)
    {Q : Over S} [GrpObj Q] [IsCommMonObj Q] {n : ℕ} (pr : Fin n → (Q ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    {L : LB Q.left} (hL : L.IsLB) (W : Matrix (Fin n) (Fin n) ℤ)
    (hW : LBIso L (LB.LinComb P (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left)
      (fun uv => W uv.1 uv.2)))
    (m : Matrix (Fin n) (Fin n) ℤ) (α : Q ⟶ Q) (hα : ∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) :
    ((W + W.transpose) * m = W → LBIso L (cubeLB Q ![𝟙 Q, α] L)) ∧
      ∀ (m' : Matrix (Fin n) (Fin n) ℤ) (α' : Q ⟶ Q), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) →
        m.transpose * (W + W.transpose) = (W + W.transpose) * m' →
        LBIso (cubeLB Q ![fst Q Q ≫ α, snd Q Q] L) (cubeLB Q ![fst Q Q, snd Q Q ≫ α'] L) := by
  refine ⟨fun hm => ?_, fun m' α' hα' hm' => ?_⟩
  · obtain ⟨β, hpt, hcube⟩ := exists_form hP hs Q (hb Q) pr hpr hL W hW
    have hc : (cubeLB Q ![𝟙 Q, α] L).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL hc).1 ?_
    have e0 := hpt (𝟙 Q)
    rw [Over.id_left, pull_id] at e0
    have hY := ofMul_comp_matrix pr m α hα (𝟙 Q)
    have hR := form_right β (W + W.transpose) m (fun u => Additive.ofMul (pr u)) (fun u => Additive.ofMul (pr u))
    simp only [Category.id_comp] at e0 hY
    rw [e0, hcube (𝟙 Q) α hc]
    simp only [Category.id_comp]
    rw [hY, hR, hm]
  · obtain ⟨β, -, hcube⟩ := exists_form hP hs (Q ⊗ Q) (hb (Q ⊗ Q)) pr hpr hL W hW
    have h1 : (cubeLB Q ![fst Q Q ≫ α, snd Q Q] L).IsLB := LB.isLB_linComb hL _ _
    have h2 : (cubeLB Q ![fst Q Q, snd Q Q ≫ α'] L).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff h1 h2).1 ?_
    have hl := form_left β (W + W.transpose) m (fun u => Additive.ofMul (fst Q Q ≫ pr u))
      (fun u => Additive.ofMul (snd Q Q ≫ pr u))
    have hr := form_right β (W + W.transpose) m' (fun u => Additive.ofMul (fst Q Q ≫ pr u))
      (fun u => Additive.ofMul (snd Q Q ≫ pr u))
    rw [hcube _ _ h1, hcube _ _ h2, ofMul_comp_matrix pr m α hα (fst Q Q), ofMul_comp_matrix pr m' α' hα' (snd Q Q), hl, hr, hm']

end Square

theorem matrix_primitive_adjoint : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → ∀ (m : Matrix (Fin 8) (Fin 8) ℤ) (α : P.A ⟶ P.A), (∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → ((W + W.transpose) * m = W → LBIso P.L (cubeLB P.A ![𝟙 P.A, α] P.L)) ∧ ∀ (m' : Matrix (Fin 8) (Fin 8) ℤ) (α' : P.A ⟶ P.A), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) → m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB P.A ![fst P.A P.A ≫ α, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ α'] P.L) := by
  intro hΘ W K _ o _ s h k ζ c P pr hpr huniv hW m α hα
  have : IsCommMonObj P.A := P.isAb.comm
  exact primitive_adjoint c.isLB c.symm
    (fun T x x' y => siegPre_bundle_mul_left hΘ K o s h k ζ c P pr hpr huniv T x x' y) pr hpr P.isLB W hW m α hα

end GlobalTheory.PowerAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgClosedJoinOfMemRange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

private theorem exists_algClosed_compositum {k K K₀ : Type} [Field k] [Field K] [Field K₀]
    (φ : k →+* K) (ψ : k →+* K₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : K₀ →+* Ω),
      i.comp φ = j.comp ψ := by
  letI : Algebra k K := φ.toAlgebra
  letI : Algebra k K₀ := ψ.toAlgebra
  haveI : Nontrivial (K ⊗[k] K₀) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K K₀
      φ.injective ψ.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] K₀)
  letI : Field (K ⊗[k] K₀ ⧸ m) := Ideal.Quotient.field m
  let emb : K ⊗[k] K₀ →+* AlgebraicClosure (K ⊗[k] K₀ ⧸ m) :=
    (algebraMap (K ⊗[k] K₀ ⧸ m) (AlgebraicClosure (K ⊗[k] K₀ ⧸ m))).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure (K ⊗[k] K₀ ⧸ m), inferInstance, inferInstance,
    emb.comp Algebra.TensorProduct.includeLeftRingHom,
    emb.comp (Algebra.TensorProduct.includeRight : K₀ →ₐ[k] K ⊗[k] K₀).toRingHom, ?_⟩
  ext a
  simp only [RingHom.comp_apply]
  congr 1
  show (algebraMap k K a) ⊗ₜ[k] (1 : K₀) = (1 : K) ⊗ₜ[k] (algebraMap k K₀ a)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

private theorem pt_eq_lemma_2 {K : Type} [Field K] (q r : PrimeSpectrum K) : q = r :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans (Ideal.eq_bot_of_prime r.asIdeal).symm)

theorem exists_algClosed_join_of_mem_range {S : Scheme.{0}} {K K₀ : Type} [Field K] [Field K₀]
    (x : Sp K ⟶ S) (x₀ : Sp K₀ ⟶ S) (p : Sp K) (p₀ : Sp K₀) (h : x p = x₀ p₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : K₀ →+* Ω),
      spMap i ≫ x = spMap j ≫ x₀ := by
  have e : p = IsLocalRing.closedPoint K := pt_eq_lemma_2 _ _
  have e₀ : p₀ = IsLocalRing.closedPoint K₀ := pt_eq_lemma_2 _ _
  subst e e₀
  have hx := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S x
  have hx₀ := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K₀ S x₀
  generalize S.descResidueField (Scheme.stalkClosedPointTo x) = φ at hx
  generalize S.descResidueField (Scheme.stalkClosedPointTo x₀) = φ₀ at hx₀
  obtain ⟨Ω, hΩ, hΩc, i, j, hij⟩ := exists_algClosed_compositum φ.hom ((S.residueFieldCongr h).hom ≫ φ₀).hom
  refine ⟨Ω, hΩ, hΩc, i, j, ?_⟩
  have hx₀' : Spec.map ((S.residueFieldCongr h).hom ≫ φ₀) ≫
      S.fromSpecResidueField (x (IsLocalRing.closedPoint K)) = x₀ := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField, hx₀]
  have hc : φ ≫ CommRingCat.ofHom i = ((S.residueFieldCongr h).hom ≫ φ₀) ≫ CommRingCat.ofHom j := by
    ext a
    exact RingHom.congr_fun hij a
  show Spec.map (CommRingCat.ofHom i) ≫ x = Spec.map (CommRingCat.ofHom j) ≫ x₀
  conv_lhs => rw [← hx]
  conv_rhs => rw [← hx₀']
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hc]

theorem geoGood_commonFibres : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t t' : TObj g k J b s), GeoGood t t' {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (u : TObj g k J b (x ≫ s)), p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x} := by
  intro o _ g k J b S s t t' K _ x hx
  obtain ⟨K₁, hK₁, x₁, u₁, ⟨p₁, hp₁⟩, hu, hu'⟩ := hx ⟨IsLocalRing.closedPoint K, rfl⟩
  obtain ⟨Ω, hΩ, hΩc, i, j, hij⟩ :=
    exists_algClosed_join_of_mem_range x x₁ (IsLocalRing.closedPoint K) p₁ hp₁.symm
  obtain ⟨u, hu₀⟩ := GlobalTheory.tObj_pull o g k J b (Sp K₁) (Sp Ω) (x₁ ≫ s) (spMap i ≫ x ≫ s) (spMap j) u₁
    (by rw [← Category.assoc, ← hij, Category.assoc])
  have hT := ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g k J b S (Sp K₁) (Sp Ω) s (x₁ ≫ s) (spMap i ≫ x ≫ s) t u₁ u).2
    x₁ (spMap j) hu).1 hu₀
  have hT' := ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g k J b S (Sp K₁) (Sp Ω) s (x₁ ≫ s) (spMap i ≫ x ≫ s) t' u₁ u).2
    x₁ (spMap j) hu').1 hu₀
  rw [← hij] at hT hT'
  obtain ⟨ψ, hψ⟩ := (tMap_iff u t _).1 hT
  obtain ⟨ψ', hψ'⟩ := (tMap_iff u t' _).1 hT'
  exact ⟨Ω, hΩ, hΩc, i, spMap i ≫ x ≫ s, u, ψ, ψ', hψ, hψ'⟩

end GlobalTheory.TUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsConstMulOfIsFnPowNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_const_mul_of_isFnPow_ne_zero (hH : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    (θ : (Fin P.g → ℂ) → ℂ) (hθ : θ ≠ 0) (s : (lbPow P.L 1).Sec) (hs : u.IsFnPow 1 s θ) (t : (lbPow P.L 1).Sec) :
    ∃ a : ℂ, ∀ j, t.f j = constFn P.A.hom _ a * s.f j := by
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hH ℂ P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  obtain ⟨a, ha, -⟩ := hβ s
  obtain ⟨b, hb, -⟩ := hβ t
  have hc : ∀ U : P.A.left.Opens, ∃ e : ℂ →+* Γ(P.A.left, U), ∀ x, constFn P.A.hom U x = e x := fun U =>
    ⟨((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ P.A.hom.appLE ⊤ U (fun _ _ => trivial)).hom, fun _ => rfl⟩
  have ha0 : a i₀ ≠ 0 := by
    intro h0
    apply hθ
    funext z
    have hm : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⊤ : P.A.left.Opens) := trivial
    rw [← P.isLB.cover] at hm
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    have hi₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i := (top_le_preimage_iff_mem _ _).2 hi
    have hi₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) :=
      (top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => hi)
    have e := hs (fun _ => i) z hi₂
    obtain ⟨c, hc'⟩ := hc ((lbPow P.L 1).U (fun _ => i))
    have e0 := (ha (fun _ => i)).trans (su _)
    rw [h0, hc', map_zero, zero_mul] at e0
    have e1 := e.symm.trans ((congrArg (valAt' _ _) e0).trans (valAt'_zero _ _))
    rw [pow_one] at e1
    exact (mul_eq_zero.1 e1).resolve_right (u.fr_ne i z hi₁)
  refine ⟨b i₀ / a i₀, fun j => ?_⟩
  obtain ⟨c, hc'⟩ := hc ((lbPow P.L 1).U j)
  rw [ha, hb, su, su, hc', hc', hc', ← _root_.mul_assoc, ← map_mul, div_mul_cancel₀ _ ha0]

theorem exists_isGenSec_of_isThetaFn : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T), u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → ∃ th : LB.Sec (Out.LPow P.A P.L 1 T), Out.IsGenSec P.A P.L 1 th ∧ (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L 1 T).U j) (th.f j) = θ z * u.fr (j 0) z ^ (1 : ℤ)) := by
  intro hL hL2 hG hU P u Hm χ θ T _ p hAH hθ hne
  obtain ⟨-, -, -, -, -, -, -, hsec, -⟩ := _root_.GlobalTheory.AnyAppellHumbert.isAH_properties hL hL2 hG hU P u Hm χ hAH
  obtain ⟨s, hs, -⟩ := (hsec 1).2 θ hθ
  have hT : ∀ {X : Over (Sp ℂ)} (f g : X ⟶ T), f = g := fun f g =>
    Over.OverMorphism.ext ((cancel_mono T.hom).1 ((Over.w f).trans (Over.w g).symm))
  let ρ : P.A ⟶ T ⊗ P.A := lift (toUnit _ ≫ p) (𝟙 _)
  have r₂ : ρ ≫ snd T P.A = 𝟙 _ := lift_snd _ _
  have r₃ : snd T P.A ≫ ρ = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, Category.id_comp])
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) r₂
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := congrArg (fun q => q.left) r₃
  have ρ₁ : ρ.left ≫ (fst T P.A).left ≫ T.hom = P.A.hom := Over.w (ρ ≫ fst T P.A)
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  obtain ⟨th, hth⟩ := PowSec.down_surjective P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) s
  refine ⟨th, fun t => ?_, fun j z hz => ?_⟩
  · obtain ⟨a, ha⟩ := exists_const_mul_of_isFnPow_ne_zero hL.globalSectionsRank P u θ hne s hs
      (PowSec.down P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) t)
    refine ⟨T.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a), fun j => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have hch := PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)
    refine PowSec.appLE_injective ρ.left _ _ hch ?_
    refine (ha (fun _ => k)).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (map_mul (ρ.left.appLE _ _ hch.le).hom _ _).symm)
    · have h0 : (T.hom.appTop ≫ (fst T P.A).left.appTop ≫ (T ⊗ P.A).left.presheaf.map (homOfLE le_top).op) =
          ((fst T P.A).left ≫ T.hom).appLE ⊤ (LB.wchart P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => k))
            (fun _ _ => trivial) := by
        rw [← Category.assoc, ← Scheme.Hom.comp_appTop]; rfl
      have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left ((fst T P.A).left ≫ T.hom) ⊤ _ _ (fun _ _ => trivial)
        hch.le).trans (PowSec.appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
      rw [← h0] at h1
      exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) h1).symm
    · rw [← hth]; rfl
  · obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have hch := PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)
    have hz₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => k) :=
      (top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => (top_le_preimage_iff_mem _ _).1 hz)
    have e := hs (fun _ => k) z hz₂
    have e₁ : lift p (u.ex z) = u.ex z ≫ ρ :=
      CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, lift_snd])
    have e₂ := valAt'_appLE (u.ex z).left ρ.left _ _ hch.le (th.f (fun _ => k)) hz₂
    rw [e₁, zpow_one]
    rw [← hth, pow_one] at e
    exact e₂.symm.trans e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalDerivationOfKodairaSpencerZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory

theorem exists_locDer_top_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∃ d, LocDer P₀.A.hom p m D ⊤ d := by
  intro hL P₀ u Hm χ hu R _ x₀ X p m hp hpb D s hD hs
  have key : ∀ (W : X.Opens) (f : Γ(X, W)), ∃! a : Γ(P₀.A.left, m ⁻¹ᵁ W),
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
    intro W f
    refine existsUnique_section_of_locally_regular P₀ u Hm χ hu (m ⁻¹ᵁ W) (fun z => s z W f) fun z hz => ?_
    have hz' : ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ) ∈ W := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW₀, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hz' W.isOpen
    have hle' : W₀ ≤ W := hle
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.KS.regular_of_periods_zero hL P₀ u Hm χ hu R x₀ X p m hp hpb D s hD hs W₀ hW₀ W₀ le_rfl (resG X hle' f)
    refine ⟨m ⁻¹ᵁ W₀, a, fun _ hy => hle' hy, (top_le_preimage_iff_mem ((u.ex z).left ≫ m) W₀).2 hzW₀, fun z' hz' => ?_⟩
    exact (ha z' hz').trans ((hs.der z').res W W₀ hle' hz' f)
  choose d hd hu' using key
  have ext : ∀ (W : X.Opens) (f : Γ(X, W)) (a : Γ(P₀.A.left, m ⁻¹ᵁ W)),
      (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f) → d W f = a :=
    fun W f a h => (hu' W f a h).symm
  refine ⟨d, ⟨fun W _ f f' => ext W _ _ fun z hz => ?_, fun W _ f f' => ext W _ _ fun z hz => ?_,
    fun W W' i _ f => ext W' _ _ fun z hz => ?_, fun W _ r => ext W _ _ fun z hz => ?_⟩⟩
  · rw [valAt'_add, hd W f z hz, hd W f' z hz, (hs.der z).add W hz]
  · rw [valAt'_add, valAt'_mul, valAt'_mul, valAt'_comp, valAt'_comp, hd W f z hz, hd W f' z hz,
      (hs.der z).mul W hz]
  · rw [(hs.der z).res W W' i hz, ← hd W f z fun _ hy => i (hz hy)]
    exact valAt'_res _ _ _ hz
  · have e : constFn p W r = resG X le_top (constFn p ⊤ r) := by
      unfold constFn
      exact (congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
        (Scheme.Hom.appLE_map p (U := ⊤) (V := ⊤) (V' := W) le_top (homOfLE le_top).op)).symm
    rw [e, (hs.der z).res ⊤ W le_top hz, hs.base]
    exact valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalPeriodLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_local_period_lift :
    ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g → ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range) ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀ a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a))) :=
  fun hT hL => _root_.GlobalTheory.LocLift.holomorphic_map_lifts_to_periods hT hL
    (fun k _ X s hs => by
      obtain ⟨hr, hn, hnoe⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k X s hs
      exact ⟨hr, IsNormalScheme.of_pred hn, hnoe⟩)
    obj_isAbelianScheme_dim_rigidified_sym obj_pull RelExp.exists_relative_exp latContinuation
    holomorphic_diagonalisation (torsion_eq_and_weilIs_of_isHolTo hL)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmetricBiadditiveBundleEighthPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_biadditive_bundle_eighthPower : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsE8 W → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → (∀ m m', m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB G ![fst G G ≫ ρ m, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ ρ m'] L)) → (∀ m, (W + W.transpose) * m = W → LBIso L (cubeLB G ![𝟙 G, ρ m] L)) → ∃ P : LB (G2 A).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) ∧ LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.EighthPower.main | exact GlobalTheory.EighthPower.main | (intros; apply GlobalTheory.EighthPower.main <;> assumption)
end

