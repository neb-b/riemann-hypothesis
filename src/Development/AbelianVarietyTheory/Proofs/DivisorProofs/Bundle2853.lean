module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernRepresentativeContractionOfOrthogonal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ChernRep

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem isContr_add {z z' : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B} {κ κ' : Fn1 A}
    (h : IsContr z v κ) (h' : IsContr z' v κ') : IsContr (z + z') v (κ.add κ') := by
  unfold IsContr at h h' ⊢
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  simp only [Fn1.add, Pi.add_apply, h D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ,
    h' D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub]
  abel

theorem isContr_sum {n : ℕ} {z : Fin n → C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B}
    {κ : Fin n → Fn1 A} (h : ∀ k, IsContr (z k) v (κ k)) :
    IsContr (∑ k, z k) v (fun D _ _ D' _ _ φ x ↦ ∑ k, κ k D D' φ x) := by
  unfold IsContr at h ⊢
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun k _ ↦ h k D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have key : ∀ g : Fin n → TrivSqZeroExt D' D', ∑ k, (g k).snd = (∑ k, g k).snd := fun g ↦
    (map_sum (TrivSqZeroExt.sndHom D' D') g Finset.univ).symm
  exact key fun k ↦ z k _ _ _ s τ - z k _ _ _ a s' - z k _ _ _ i τ + z k _ _ _ b i'

theorem isContr_eq {z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B} (hv : IsTangent v)
    {κ κ' : Fn1 A} (h : IsContr z v κ) (h' : IsContr z v κ') (D : Type) [CommRing D] [Algebra R D]
    (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    κ D D' φ x = κ' D D' φ x := by
  obtain ⟨s, i, s', i', a, b, τ, hs, hi, hs', hi', ha, hb, hτ⟩ :=
    (GlobalTheory.PtExt.ContrMor.exists_contr R A B v hv).1 D D' φ x
  exact (h D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ).trans
    (h' D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ).symm

theorem sum_split {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (Φ : M →ₗ[R] N →ₗ[R] P) {n : ℕ} (a a₁ : Fin n → M) (b b₁ : Fin n → N)
    (h : ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0) :
    ∑ k, Φ (a k) (b k) = ∑ k, Φ (a₁ k) (b k) + ∑ k, Φ (a k - a₁ k) (b₁ k) := by
  have h0 : ∑ k, Φ (a k - a₁ k) (b k - b₁ k) = 0 := by
    have := congrArg (TensorProduct.lift Φ) h
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, TensorProduct.lift.tmul, map_zero] using this
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [map_sub, LinearMap.sub_apply]
  abel

theorem fv_sub_sum {X : Over (Sp R)} {n : ℕ} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (t : Fin n → R)
    (u : Fin n → Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type)
    [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (f - ∑ k, t k • u k) D D' φ x = fv f D D' φ x - ∑ k, algebraMap R D' (t k) * fv (u k) D D' φ x := by
  simp only [fv, ev, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
  rfl

theorem fv_smul {X : Over (Sp R)} (t : R) (u : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D]
    [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (t • u) D D' φ x = algebraMap R D' t * fv u D D' φ x := by
  simp only [fv, ev, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]

section Rep

variable (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
  (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)


omit [GrpObj A] [GrpObj B] in
def cupPr (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)


omit [GrpObj A] [GrpObj B] in
theorem mk_cupPr (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    CatCoh.H2.mk _ (cupPr m₁ m₂ a b) = cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ a))
      (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ b)) := rfl

def cupPrim (A B : Over (Sp R)) [GrpObj A] [GrpObj B] :
    primDR A →ₗ[R] primDR B →ₗ[R] CatCoh.H2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  (cup _).compl₁₂ (pullOver (dp0 R) (𝟙 _) (fst A B) ∘ₗ (primDR A).subtype)
    (pullOver (dp0 R) (𝟙 _) (snd A B) ∘ₗ (primDR B).subtype)

theorem cupPrim_apply (a : primDR A) (b : primDR B) : cupPrim A B a b =
    cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) a.1) (pullOver (dp0 R) (𝟙 _) (snd A B) b.1) := rfl

theorem mk_cupPr_prim {a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))} {x : primDR A}
    {y : primDR B} (ha : CatCoh.H1.mk _ a = x.1) (hb : CatCoh.H1.mk _ b = y.1) :
    CatCoh.H2.mk _ (cupPr m₁ m₂ a b) = cupPrim A B x y := by
  rw [mk_cupPr, cupPrim_apply, ha, hb]

variable {n : ℕ} (α : Fin n → Form (A.hom ≫ 𝟙 _)) (β : Fin n → Form (B.hom ≫ 𝟙 _))
  (a' : Fin n → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b' : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))


omit [GrpObj A] [GrpObj B] in
def rep : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  ∑ k, cupPr m₁ m₂ (α k).1 (b' k) + ∑ k, cupPr m₁ m₂ (a' k) (β k).1


omit [GrpObj A] [GrpObj B] in
theorem rep_val : (rep m₁ m₂ α β a' b').1 =
    ∑ k, (cupPr m₁ m₂ (α k).1 (b' k)).1 + ∑ k, (cupPr m₁ m₂ (a' k) (β k).1).1 := by
  rw [rep, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_sum]


omit [GrpObj A] [GrpObj B] in
theorem mk_rep : CatCoh.H2.mk _ (rep m₁ m₂ α β a' b') =
    ∑ k, CatCoh.H2.mk _ (cupPr m₁ m₂ (α k).1 (b' k)) + ∑ k, CatCoh.H2.mk _ (cupPr m₁ m₂ (a' k) (β k).1) :=
  ((CatCoh.H2.mk _).map_add _ _).trans (congrArg₂ (· + ·) (map_sum _ _ _) (map_sum _ _ _))


omit [GrpObj A] [GrpObj B] in
theorem rep_triv (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (p : T ⟶ T') (q : T' ⟶ T'') (hT : T.J = ⊥)
    (hT' : T'.J = ⊥) (hT'' : T''.J = ⊥) : (rep m₁ m₂ α β a' b').1 T T' T'' p q = 0 := by
  have h1 : ∀ k, (cupPr m₁ m₂ (α k).1 (b' k)).1 T T' T'' p q = 0 := fun k ↦ by
    rw [cupPr, cupZ_apply,
      show (m₁.coef.pullbackOneCocycle (α k).1).1 T T' p = 0 from (α k).2 (m₁.functor.map p) hT hT', map_zero, zero_mul]
  have h2 : ∀ k, (cupPr m₁ m₂ (a' k) (β k).1).1 T T' T'' p q = 0 := fun k ↦ by
    rw [cupPr, cupZ_apply,
      show (m₂.coef.pullbackOneCocycle (β k).1).1 T' T'' q = 0 from (β k).2 (m₂.functor.map q) hT' hT'', mul_zero]
  rw [rep_val]
  simp only [Pi.add_apply, Finset.sum_apply, h1, h2, Finset.sum_const_zero, add_zero]

theorem rep_contr {v : epsR R ⟶ B} (hv : IsTangent v) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)))
    (hcl : CatCoh.H1.mk _ (f - ∑ k, tanVal v (β k) • a' k) ∈ F1 (A.hom ≫ 𝟙 _)) (κ : Fn1 A)
    (hκ : IsContr (rep m₁ m₂ α β a' b').1 v κ) : Cohom (whole A) κ (fv f).neg := by
  obtain ⟨-, hex⟩ := GlobalTheory.PtExt.ContrMor.exists_contr R A B v hv
  choose κX hκX using fun k ↦ hex (cupPr m₁ m₂ (α k).1 (b' k)).1
  choose κY hκY using fun k ↦ hex (cupPr m₁ m₂ (a' k) (β k).1).1
  rw [rep_val] at hκ
  have hsC := isContr_add (isContr_sum hκX) (isContr_sum hκY)
  have hX0 := fun k ↦ GlobalTheory.PtExt.contr_cup_form_eq_zero R A B m₁ m₂ v hv (α k) (b' k) (κX k) (hκX k)
  have hYc := fun k ↦ GlobalTheory.PtExt.cohom_contr_cupA R A B m₁ m₂ v hv (a' k) (β k) (κY k) (hκY k)
  unfold Cohom at hYc
  choose cY hcY using hYc
  obtain ⟨k₀, hk₀⟩ := (GlobalTheory.PtExt.mem_hodgeFiltration_iff_pointwiseCoboundary R A _).1 hcl
  refine ⟨fun D _ _ x ↦ k₀ D x + ∑ k, cY k D x, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := isContr_eq hv hκ hsC D D' φ x
  have e2 := hk₀ D D' φ x (sm_whole x)
  have e3 : ∀ k, κY k D D' φ x = cY k D' (spOver φ ≫ x) - φ (cY k D x) -
      algebraMap R D' (tanVal v (β k)) * fv (a' k) D D' φ x := fun k ↦ by
    have h3 := hcY k D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg, fv_smul, map_neg] at h3
    linear_combination h3
  rw [fv_sub_sum] at e2
  simp only [Fn1.add, Fn1.neg, hX0, Finset.sum_const_zero, zero_add] at e1 ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_add (f := _), map_sum]
  simp only [e3, Finset.sum_sub_distrib]
  linear_combination e2

end Rep

theorem apply_sub_sum {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {n : ℕ}
    (a a₁ : Fin n → M) (b b₁ : Fin n → N) (h : ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0) (x : M →ₗ[R] R)
    (y : N →ₗ[R] R) (hx : ∀ k, x (a₁ k) = 0) (c : M) (hc : x c = ∑ k, x (a k) * y (b k)) :
    x (c - ∑ k, y (b₁ k) • (a k - a₁ k)) = 0 := by
  have e := sum_split ((LinearMap.mul R R).compl₁₂ x y) a a₁ b b₁ h
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at e
  simp only [map_sub, hx, sub_zero, zero_mul, Finset.sum_const_zero, zero_add] at e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, hc, e]
  simp only [map_smul, map_sub, hx, sub_zero, smul_eq_mul, mul_comm, sub_self]

theorem mk_sub_sum {n : ℕ} {f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {c : primDR A} (hf : CatCoh.H1.mk _ f = c.1)
    {a' : Fin n → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {a : Fin n → primDR A} (ha : ∀ k, CatCoh.H1.mk _ (a' k) = (a k).1)
    (t : Fin n → R) : CatCoh.H1.mk _ (f - ∑ k, t k • a' k) = (c - ∑ k, t k • a k : primDR A).1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, hf, Submodule.coe_sub, Submodule.coe_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, ha k, Submodule.coe_smul]

end GlobalTheory.PtExt.ChernRep


open GlobalTheory.PtExt.ChernRep in
theorem GlobalTheory.PtExt.exists_chernRep_contr_of_orth : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∃ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) ∧ (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) ∧ ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (whole A) κ (fv f).neg := by
  intro hHDR R _ A B _ _ g hA hB hgA hgB P hP pf hpf horth h' v hv c hc f hf
  obtain ⟨hFree, hHodge, -⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange hHDR
  obtain ⟨-, hprA, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hFree hA hgA
  obtain ⟨-, hprB, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hFree hB hgB
  obtain ⟨-, hCA, -⟩ := hHodge R A g hA hgA
  obtain ⟨-, hCB, -⟩ := hHodge R B g hB hgB
  obtain ⟨n, a, b, hch, hab⟩ := hpf
  have L := GlobalTheory.tensor_mem_of_dualAnnihilator R (primDR A) (primDR B) (PrimitiveSubmodule A) (PrimitiveSubmodule B) hCA hCB
  obtain ⟨a₁, b₁, ha₁, hb₁, hsum⟩ := L.2 n a b fun x hx y hy ↦ (hab x y).symm.trans (horth x hx y hy)
  have eα : ∀ k, ∃ α : Form (A.hom ≫ 𝟙 _), Form.cl _ α = (a₁ k).1 := fun k ↦ by
    have h := ha₁ k
    rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range] at h
    exact h
  choose α hα using eα
  have eβ : ∀ k, ∃ β : Form (B.hom ≫ 𝟙 _), Form.cl _ β = (b₁ k).1 := fun k ↦ by
    have h := hb₁ k
    rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range] at h
    exact h
  choose β hβ using eβ
  choose b' hb' using fun k ↦ CatCoh.H1.mk_surjective (O (dp0 R) (B.hom ≫ 𝟙 _)) (b k).1
  choose a' ha' using fun k ↦ CatCoh.H1.mk_surjective (O (dp0 R) (A.hom ≫ 𝟙 _)) (a k - a₁ k).1
  have m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  refine ⟨rep m₁ m₂ α β a' b', ?_, rep_triv m₁ m₂ α β a' b', rep_contr m₁ m₂ α β a' b' hv.1 f ?_⟩
  · have hz : CatCoh.H2.mk _ (rep m₁ m₂ α β a' b') = ∑ k, cupPrim A B (a k) (b k) :=
      ((mk_rep m₁ m₂ α β a' b').trans (congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun k _ ↦ mk_cupPr_prim m₁ m₂ (hα k) (hb' k))
        (Finset.sum_congr rfl fun k _ ↦ mk_cupPr_prim m₁ m₂ (ha' k) (hβ k)))).trans
        (sum_split (cupPrim A B) a a₁ b b₁ hsum).symm
    exact hz ▸ hch
  · have ht : (fun k ↦ tanVal v (β k)) = fun k ↦ h' (b₁ k) := funext fun k ↦ by
      have hm : Form.cl _ (β k) ∈ primDR B := (hβ k).symm ▸ (b₁ k).2
      exact (hv.2 (β k) hm).symm.trans (congrArg h' (Subtype.ext (hβ k)))
    have hd : c - ∑ k, h' (b₁ k) • (a k - a₁ k) ∈ PrimitiveSubmodule A := L.1 _ fun x hx ↦
      apply_sub_sum a a₁ b b₁ hsum x h' (fun k ↦ (Submodule.mem_dualAnnihilator _).1 hx _ (ha₁ k)) c
        ((hc x hx).symm.trans (hab x h'))
    rw [mk_sub_sum hf ha' fun k ↦ tanVal v (β k)]
    simp only [fun k ↦ congrFun ht k]
    exact hd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorBundleSectionGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClearSecB

theorem exists_app_eq_of_local {X Y : Scheme.{0}} (h : Y ⟶ X) (hinj : ∀ W : X.Opens, Function.Injective (h.app W).hom)
    (W : X.Opens) (f : Γ(Y, h ⁻¹ᵁ W))
    (hf : ∀ x ∈ W, ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧ ∃ a : Γ(X, V),
      (h.app V).hom a = (Y.presheaf.map (homOfLE (fun _ hy => hV hy : h ⁻¹ᵁ V ≤ h ⁻¹ᵁ W)).op).hom f) :
    ∃ a : Γ(X, W), (h.app W).hom a = f := by
  choose V hV hxV a ha using hf
  have gp : ∀ (U : X.Opens) (c : Γ(X, U)) (y : Y), h y ∈ U → gs (𝟙 Y) y (h ⁻¹ᵁ U) ((h.app U).hom c) = gs h y U c :=
    fun U c y hy => (gs_pull (𝟙 Y) h y U hy c).trans (by rw [Category.id_comp])
  have gx : ∀ x (hx : x ∈ W) (y : Y), h y ∈ V x hx → gs h y (V x hx) (a x hx) = gs (𝟙 Y) y (h ⁻¹ᵁ W) f := by
    intro x hx y hy
    have hy' : (𝟙 Y) y ∈ h ⁻¹ᵁ V x hx := hy
    exact (gp _ _ y hy).symm.trans ((congrArg (gs (𝟙 Y) y _) (ha x hx)).trans (gs_res (𝟙 Y) y _ hy' _))
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : W => V x.1 x.2) W (fun x => homOfLE (hV x.1 x.2))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV x hx⟩) (fun x => a x.1 x.2) (fun x x' => hinj _ (fn_ext
      fun y hy => by
        have hy' : h y ∈ V x.1 x.2 ⊓ V x'.1 x'.2 := hy
        exact (gp _ _ y hy').trans ((gs_res h y _ hy' _).trans ((gx _ _ y hy'.1).trans ((gx _ _ y hy'.2).symm.trans
          ((gs_res h y _ hy' _).symm.trans (gp _ _ y hy').symm))))))
  refine ⟨s, fn_ext fun y hy => ?_⟩
  have hy' : h y ∈ W := hy
  exact (gp _ _ y hy').trans ((gs_res h y (hV _ hy') (hxV _ hy') s).symm.trans
    ((congrArg (gs h y _) (hs ⟨h y, hy'⟩)).trans (gx _ _ y (hxV _ hy'))))

theorem exists_mul_eq_app {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (V : Q.P.A.left.Opens)
    (hV : IsAffineOpen V) (f : Γ((DegPre.BF Q (FractionRing R)).left, (DegPre.prB Q (FractionRing R)).left ⁻¹ᵁ V)) :
    ∃ r : R, r ≠ 0 ∧ ∃ a : Γ(Q.P.A.left, V), ((DegPre.prB Q (FractionRing R)).left.app V).hom a =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) * f := by
  have eT : (TF (R := R) (FractionRing R)).hom = jK R := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have H0 := (IsPullback.of_hasPullback (TF (R := R) (FractionRing R)).hom Q.P.A.hom).flip
  have H : IsPullback (DegPre.prB Q (FractionRing R)).left (pullback.fst (TF (R := R) (FractionRing R)).hom Q.P.A.hom)
      Q.P.A.hom (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (CommRingCat.of (FractionRing R))))) :=
    IsPullback.of_iso H0 (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; exact eT)
  have hloc := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := CommRingCat.of R) (L := CommRingCat.of (FractionRing R))
    (nonZeroDivisors R) H hV
  letI := ((DegPre.prB Q (FractionRing R)).left.app V).hom.toAlgebra
  obtain ⟨⟨a, _, r, hr, rfl⟩, e⟩ := IsLocalization.surj
    ((nonZeroDivisors (CommRingCat.of R)).map (GlobalTheory.QCoh.Qcqs.baseRingHom Q.P.A.hom V).hom) f
  refine ⟨r, nonZeroDivisors.ne_zero hr, a, ?_⟩
  have e2 : algebraMap Γ(Q.P.A.left, V) Γ((DegPre.BF Q (FractionRing R)).left, (DegPre.prB Q (FractionRing R)).left ⁻¹ᵁ V)
      ((GlobalTheory.QCoh.Qcqs.baseRingHom Q.P.A.hom V).hom r) =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) := by
    show ((DegPre.prB Q (FractionRing R)).left.app V).hom _ = _
    rw [GlobalTheory.QCoh.Qcqs.app_baseRingHom, ← GlobalTheory.QCoh.Qcqs.baseRingHom_res _ (le_top : _ ≤ ⊤), GlobalTheory.QCoh.Qcqs.baseRingHom_top,
      Over.w]
    rfl
  rw [e2] at e
  exact e.symm.trans (mul_comm _ _)

theorem exists_clear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))), ∃ r : R, r ≠ 0 ∧ ∃ σ : Q.SecB k β, ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ (x ≫ (DegPre.prB Q (FractionRing R)).left) z J = gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * sval s x z J := by
  intro R _ _ _ Q k β s
  classical
  set p := (DegPre.prB Q (FractionRing R)).left with hp
  have hφ : ∀ i, DegPre.famφ Q (FractionRing R) β i = p ≫ Q.famφB β i := ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq Q _ β
  have hw : ∀ j, LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j = p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) j := by
    intro j
    have e : DegPre.famφ Q (FractionRing R) β = fun k => p ≫ Q.famφB β k := funext hφ
    rw [e]
    ext y
    simp [LB.wchart]
  have inj : ∀ W, Function.Injective (p.app W).hom := fun W => GlobalTheory.IntegralExpansion.prB_app_injective Q W
  have hpw : p ≫ Q.P.A.hom = (DegPre.BF Q (FractionRing R)).hom := Over.w _
  have gp : ∀ (U : Q.P.A.left.Opens) (a : Γ(Q.P.A.left, U)) (y : (DegPre.BF Q (FractionRing R)).left), p y ∈ U →
      gs (𝟙 _) y (p ⁻¹ᵁ U) ((p.app U).hom a) = gs p y U a := fun U a y h =>
    (gs_pull (𝟙 _) p y U h a).trans (by rw [Category.id_comp])
  have gsc : ∀ (y : (DegPre.BF Q (FractionRing R)).left) (c : R),
      gs p y ⊤ (Out.scal Q.P.A.hom c) = gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom c) := fun y c =>
    (gs_pull p Q.P.A.hom y ⊤ trivial _).trans ((by rw [hpw, Category.id_comp] :
      gs (p ≫ Q.P.A.hom) y ⊤ _ = gs (𝟙 _ ≫ (DegPre.BF Q (FractionRing R)).hom) y ⊤ _).trans
        (gs_pull (𝟙 _) (DegPre.BF Q (FractionRing R)).hom y ⊤ trivial _).symm)
  have gmul : ∀ (y : (DegPre.BF Q (FractionRing R)).left) (c c' : R),
      gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom (c * c')) =
        gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom c) * gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom c') :=
    fun y c c' => by rw [← gs_mul _ y ⊤ trivial]; simp only [Out.scal, map_mul]
  have htr : ∀ (y : (DegPre.BF Q (FractionRing R)).left) (i j : Fin 4 → Q.P.L.ι),
      trF (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k) (𝟙 _) y i j =
        trF (Q.famφB β) (DegPre.famε k) p y i j := fun y i j => by
    simp only [trF, hφ, Category.id_comp]
  have : IsProper Q.P.A.hom := Q.P.isAb.proper
  have : CompactSpace Q.P.A.left := QuasiCompact.compactSpace_of_compactSpace Q.P.A.hom
  have hb : ∀ b : Q.P.A.left, ∃ j : Fin 4 → Q.P.L.ι, ∃ V : Q.P.A.left.Opens, IsAffineOpen V ∧ b ∈ V ∧
      V ≤ LB.wchart Q.P.L (Q.famφB β) j := by
    intro b
    choose i hi using fun k : Fin 4 => exists_chart Q.P.isLB (Q.famφB β k b)
    have hb : b ∈ LB.wchart Q.P.L (Q.famφB β) i := Set.mem_iInter.2 hi
    obtain ⟨V, hV, hbV, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Q.P.A.left.isBasis_affineOpens) hb
    exact ⟨i, V, hV, hbV, hle⟩
  choose jb Vb hVa hbV hVle using hb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun b => (Vb b : Set Q.P.A.left)) (fun b => (Vb b).isOpen)
    (fun b _ => Set.mem_iUnion.2 ⟨b, hbV b⟩)
  have hA : ∀ b, ∃ r : R, r ≠ 0 ∧ ∃ a : Γ(Q.P.A.left, Vb b), (p.app (Vb b)).hom a =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) *
        ((DegPre.BF Q (FractionRing R)).left.presheaf.map (homOfLE (le_trans (show p ⁻¹ᵁ Vb b ≤ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) (jb b) from
          fun _ hy => hVle b hy) (hw (jb b)).ge)).op).hom (s.f (jb b)) :=
    fun b => exists_mul_eq_app Q (Vb b) (hVa b) _
  choose rb hrb ab hab using hA
  have hAg : ∀ b (y : (DegPre.BF Q (FractionRing R)).left), p y ∈ Vb b → gs p y (Vb b) (ab b) =
      gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom (rb b)) *
        gs (𝟙 _) y (LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) (jb b)) (s.f (jb b)) := by
    intro b y hy
    have hy' : (𝟙 (DegPre.BF Q (FractionRing R)).left) y ∈ p ⁻¹ᵁ Vb b := hy
    have e := congrArg (gs (𝟙 _) y (p ⁻¹ᵁ Vb b)) (hab b)
    exact (gp _ _ y hy).symm.trans (e.trans ((gs_mul _ y _ hy' _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy' _) (gs_res _ y _ hy' _))))
  set r := ∏ b ∈ t, rb b with hr_def
  have hr : r ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hrb b

  have hlift : ∀ j, ∃ a : Γ(Q.P.A.left, LB.wchart Q.P.L (Q.famφB β) j), (p.app _).hom a =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) *
        ((DegPre.BF Q (FractionRing R)).left.presheaf.map (homOfLE (hw j).ge).op).hom (s.f j) := by
    intro j
    refine exists_app_eq_of_local p inj _ _ fun x hx => ?_
    obtain ⟨b, hbt, hxb⟩ : ∃ b ∈ t, x ∈ Vb b := by simpa using ht (Set.mem_univ x)
    have le1 : Vb b ⊓ LB.wchart Q.P.L (Q.famφB β) j ≤ (LB.LinComb Q.P.L (Q.famφB β) (DegPre.famε k)).U j ⊓
        (LB.LinComb Q.P.L (Q.famφB β) (DegPre.famε k)).U (jb b) := le_inf inf_le_right (inf_le_left.trans (hVle b))
    refine ⟨Vb b ⊓ LB.wchart Q.P.L (Q.famφB β) j, inf_le_right, ⟨hxb, hx⟩,
      resTop _ (Out.scal Q.P.A.hom (∏ b' ∈ t.erase b, rb b')) *
        (Q.P.A.left.presheaf.map (homOfLE inf_le_left).op).hom (ab b) *
        (Q.P.A.left.presheaf.map (homOfLE le1).op).hom
          ((LB.LinComb Q.P.L (Q.famφB β) (DegPre.famε k)).g j (jb b)).val, ?_⟩
    refine fn_ext fun y hy => ?_
    have hpy : p y ∈ Vb b ⊓ LB.wchart Q.P.L (Q.famφB β) j := hy
    have hyj : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j := (hw j).ge hpy.2
    have hyb : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) (jb b) := (hw (jb b)).ge (hVle b hpy.1)
    have hy1 : (𝟙 (DegPre.BF Q (FractionRing R)).left) y ∈ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) j := hpy.2
    refine ((gp _ _ y hpy).trans ((gs_mul p y _ hpy _ _).trans (congrArg₂ (· * ·) ((gs_mul p y _ hpy _ _).trans
      (congrArg₂ (· * ·) ((gs_res p y le_top hpy _).trans (gsc y _)) ((gs_res p y inf_le_left hpy _).trans
        (hAg b y hpy.1)))) ((gs_res p y le1 hpy _).trans ((gs_unit p y _ (le1 hpy) _).trans
          (congrArg Units.val (gm_linComb _ _ _ p y j (jb b) hpy.2 (hVle b hpy.1)))))))).trans
      (Eq.trans ?_ ((gs_res (𝟙 _) y _ hy _).trans ((gs_mul _ y _ hy1 _ _).trans (congrArg₂ (· * ·)
        (gs_res _ y le_top hy1 _) ((gs_res _ y _ hy1 _).trans (sec_trans s (𝟙 _) y hyj hyb))))).symm)
    rw [htr, hr_def, ← Finset.mul_prod_erase t rb hbt, gmul]
    simp only [trF]
    ring
  choose σf hσf using hlift
  have hσg : ∀ j (y : (DegPre.BF Q (FractionRing R)).left), p y ∈ LB.wchart Q.P.L (Q.famφB β) j → gs p y _ (σf j) =
      gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) *
        gs (𝟙 _) y (LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j) (s.f j) := by
    intro j y hy
    have hy' : (𝟙 (DegPre.BF Q (FractionRing R)).left) y ∈ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) j := hy
    exact (gp _ _ y hy).symm.trans ((congrArg (gs (𝟙 _) y _) (hσf j)).trans ((gs_mul _ y _ hy' _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy' _) (gs_res _ y _ hy' _))))
  refine ⟨r, hr, ⟨σf, fun i j => inj _ (fn_ext fun y hy => ?_)⟩, fun Z x z J hJ => ?_⟩
  · have hpy : p y ∈ LB.wchart Q.P.L (Q.famφB β) i ⊓ LB.wchart Q.P.L (Q.famφB β) j := hy
    have hyi : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) i := (hw i).ge hpy.1
    have hyj : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j := (hw j).ge hpy.2
    refine ((gp _ _ y hpy).trans ((gs_res p y _ hpy _).trans (hσg i y hpy.1))).trans (Eq.trans ?_
      ((gp _ _ y hpy).trans ((gs_mul p y _ hpy _ _).trans (congrArg₂ (· * ·) ((gs_unit p y _ hpy _).trans
        (congrArg Units.val (gm_linComb _ _ _ p y i j hpy.1 hpy.2))) ((gs_res p y _ hpy _).trans
          (hσg j y hpy.2))))).symm)
    rw [sec_trans s (𝟙 _) y hyi hyj]
    simp only [trF, hφ, Category.id_comp]
    ring
  · have hj0 := hJ.mem (Q.famφB β) (x ≫ p)
    have hxz : x z ∈ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) (fun k => J ((x ≫ p) ≫ Q.famφB β k)) := hj0
    rw [sval_of s x z J (fun k => J ((x ≫ p) ≫ Q.famφB β k)) (fun k => by rw [hφ, Category.assoc])]
    show gs (x ≫ p) z _ (σf _) = _
    refine ((gs_pull x p z _ hj0 _).symm.trans ((congrArg (gs x z _) (hσf _)).trans ((gs_mul x z _ hxz _ _).trans
      (congrArg₂ (· * ·) (gs_res x z le_top hxz _) (gs_res x z _ hxz _))))).trans ?_
    exact congrArg (· * _) (gs_pull x _ z ⊤ trivial _)

end GlobalTheory.ClearSecB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryDivisibleOfQuasiLogDefec
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem exists_int_cob_dvd_of_defect_ev :
    ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  intro p _ O E _ _ _ hF G d c f s y hQL hs hy
  obtain ⟨hf0, -, hcob⟩ := hQL
  choose bκ _ hbκ using hcob
  set κ : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => bκ α with hκdef
  have hκ : map (algebraMap O E) κ = cob1 (up E c.μ) f := by
    ext α
    rw [coeff_map, hbκ α]
    rfl
  obtain ⟨hcoc, hκ0, hdef⟩ := _root_.GlobalTheory.QLog.integral_cob_defect_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hrel := (hdef p s hs).1
  have hμ0 := c.isLaw.const
  have hneg : cob1 c.μ (-s) = -cob1 c.μ s := by
    rw [← neg_one_smul O s, formalCoboundary_smul hμ0, neg_one_smul]
  obtain ⟨t, ht0, htd⟩ := _root_.GlobalTheory.CobModP.coboundary_mod_p p O G d c κ (-s) (-y) (hκ0 hf0) hcoc
    (fun α => by
      rw [hneg, hrel, show -((p : O) • κ - pull2 (nmul c.μ p) κ) - pull2 (nmul c.μ p) κ
        = -((p : O) • κ) by ring, map_neg, coeff_smul]
      exact (Dvd.intro _ rfl).neg_right)
    (by rw [map_neg, hy, smul_neg])
  refine ⟨t, ht0, fun α => ⟨coeff α (κ - cob1 c.μ t), Ideal.mem_span_singleton.2 (htd α), ?_⟩⟩
  have hup0 : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ0, map_zero]
  have hadd := formalCoboundary_add hup0 (f - map (algebraMap O E) t) (map (algebraMap O E) t)
  rw [sub_add_cancel] at hadd
  have hmap := (_root_.GlobalTheory.Katz.map_cob_swap_pull O d c.μ hμ0 E (algebraMap O E)).1 t
  have hsub : cob1 (up E c.μ) (f - map (algebraMap O E) t) =
      map (algebraMap O E) (κ - cob1 c.μ t) := by
    rw [map_sub, hmap, hκ]
    exact eq_sub_of_add_eq hadd.symm
  rw [hsub, coeff_map]

end GlobalTheory.QLog
end

