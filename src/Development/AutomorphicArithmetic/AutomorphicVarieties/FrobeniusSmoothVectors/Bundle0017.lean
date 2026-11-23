module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OfForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OfTrace
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zero_of_trace {G K : Type} [Monoid G] [Field K] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : Submodule.span K (Set.range ρ) = ⊤) (X : Matrix (Fin n) (Fin n) K) (hX : ∀ g, (ρ g * X).trace = 0) :
    X = 0 := by
  have hall : ∀ M : Matrix (Fin n) (Fin n) K, (M * X).trace = 0 := by
    intro M
    have hM : M ∈ Submodule.span K (Set.range ρ) := by rw [h]; trivial
    induction hM using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hX t
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul a x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  ext i j
  simpa [Matrix.trace_single_mul] using hall (Matrix.single j i 1)

private theorem span_of_trace {G C K K' : Type} [Monoid G] [CommRing C] [Field K] [Field K'] {n : ℕ}
    (f : C →+* K) (hf : Function.Injective f) (φ : C →+* K') (t : G → C)
    (ρ : G →* Matrix (Fin n) (Fin n) K) (ρ' : G →* Matrix (Fin n) (Fin n) K')
    (h : ∀ g, f (t g) = (ρ g).trace) (h' : ∀ g, φ (t g) = (ρ' g).trace)
    (hs : Submodule.span K' (Set.range ρ') = ⊤) : Submodule.span K (Set.range ρ) = ⊤ := by
  obtain ⟨g, hg⟩ := (UpperTheory.V.AlgebraTools.Det.gramIff ρ').mp hs
  refine (UpperTheory.V.AlgebraTools.Det.gramIff ρ).mpr ⟨g, fun h0 => hg ?_⟩
  have e : (Matrix.of fun a b => (ρ (g a * g b)).trace) = f.mapMatrix (Matrix.of fun a b => t (g a * g b)) := by
    ext a b
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h]
  have e' : (Matrix.of fun a b => (ρ' (g a * g b)).trace) = φ.mapMatrix (Matrix.of fun a b => t (g a * g b)) := by
    ext a b
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h']
  rw [e, ← RingHom.map_det, map_eq_zero_iff f hf] at h0
  rw [e', ← RingHom.map_det, h0, map_zero]

private theorem lift_surj {G K : Type} [Group G] [Field K] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : Submodule.span K (Set.range ρ) = ⊤) :
    Function.Surjective (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ) := by
  have : LinearMap.range (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ).toLinearMap = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.of K G g, by simp⟩
  exact LinearMap.range_eq_top.1 this

private theorem conj_of_trace {G K : Type} [Group G] [Field K] {n : ℕ} (ρ₁ ρ₂ : G →* Matrix (Fin n) (Fin n) K)
    (h₂ : Submodule.span K (Set.range ρ₂) = ⊤) (hf : ∀ g, (ρ₁ g).trace = (ρ₂ g).trace) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧ ∀ g, ρ₁ g * P = P * ρ₂ g := by
  have h₁ := span_of_trace (RingHom.id K) Function.injective_id (RingHom.id K) (fun g => (ρ₁ g).trace) ρ₁ ρ₂
    (fun _ => rfl) hf h₂
  set R₁ := MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ₁ with hR₁
  set R₂ := MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ₂ with hR₂
  have s₂ : Function.Surjective R₂ := lift_surj ρ₂ h₂
  have e1 : ∀ g, R₁ (MonoidAlgebra.of K G g) = ρ₁ g := fun g => by simp [hR₁]
  have e2 : ∀ g, R₂ (MonoidAlgebra.of K G g) = ρ₂ g := fun g => by simp [hR₂]
  have hf' : ∀ a, (R₁ a).trace = (R₂ a).trace := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g => rw [e1, e2, hf]
    | add a b ha hb => simp only [map_add (f := _), Matrix.trace_add, ha, hb]
    | smul c a ha => simp only [map_smul, Matrix.trace_smul, ha]
  have hker : ∀ a, R₂ a = 0 → R₁ a = 0 := by
    intro a ha
    refine zero_of_trace ρ₁ h₁ _ fun g => ?_
    rw [← e1, ← map_mul, hf', map_mul, ha, mul_zero, Matrix.trace_zero]
  let φ₀ := RingHom.liftOfSurjective R₂.toRingHom s₂ ⟨R₁.toRingHom, fun a ha => hker a ha⟩
  have hφ₀ : ∀ a, φ₀ (R₂ a) = R₁ a := fun a => RingHom.liftOfSurjective_comp_apply R₂.toRingHom s₂ _ a
  let φ : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K :=
    ⟨φ₀, fun c => by
      have := hφ₀ (algebraMap K _ c)
      rwa [AlgHom.commutes, AlgHom.commutes] at this⟩
  obtain ⟨J, hJ⟩ := KStar.Tree.exists_conj_of_algHom φ
  refine ⟨J, J.isUnit, fun g => ?_⟩
  have h1 := hJ (R₂ (MonoidAlgebra.of K G g))
  have e : φ (R₂ (MonoidAlgebra.of K G g)) = R₁ (MonoidAlgebra.of K G g) := hφ₀ _
  rwa [e, e1, e2] at h1

private theorem alt_two {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (P A B : Matrix (Fin 2) (Fin 2) K) (hP : IsUnit P)
    (hs : Pᵀ = -P) (h : Bᵀ * P = P * A) : A + B = A.trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have d : ∀ i, P i i = 0 := fun i => by
    have := congrFun (congrFun hs i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    exact (mul_eq_zero.1 (by linear_combination this : 2 * P i i = 0)).resolve_left h2
  have o : P 1 0 = -P 0 1 := congrFun (congrFun hs 0) 1
  have u : P 0 1 ≠ 0 := by
    have := ((Matrix.isUnit_iff_isUnit_det _).1 hP).ne_zero
    rw [Matrix.det_fin_two, d, d, o] at this
    intro h0
    simp [h0] at this
  have k := fun i j => congrFun (congrFun h i) j
  have k00 := k 0 0
  have k01 := k 0 1
  have k10 := k 1 0
  have k11 := k 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, d, o] at k00 k01 k10 k11
  ext i j
  apply mul_left_cancel₀ u
  fin_cases i <;> fin_cases j <;> simp [Matrix.trace_fin_two, -mul_eq_mul_left_iff, -mul_eq_zero]
  · linear_combination k01
  · linear_combination k11
  · linear_combination -k00
  · linear_combination -k10

private theorem not_alt {G K : Type} [Group G] [Field K] (h2 : (2 : K) ≠ 0) (ρ : G →* Matrix (Fin 2) (Fin 2) K)
    (hs : Submodule.span K (Set.range ρ) = ⊤)
    (h : ∀ g x, (ρ x * ρ g).trace + (ρ x * (Jmat (R := K) 2 * (ρ g)ᵀ * Jmat (R := K) 2)).trace = (ρ g).trace * (ρ x).trace) :
    False := by
  have h1 : ∀ g, ρ g 0 1 = 0 := fun g => by
    have := zero_of_trace ρ hs (ρ g + Jmat (R := K) 2 * (ρ g)ᵀ * Jmat (R := K) 2 - (ρ g).trace • 1) fun x => by
      rw [Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add, h, Matrix.mul_smul, Matrix.mul_one,
        Matrix.trace_smul, smul_eq_mul, sub_self]
    have e := congrFun (congrFun this 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Jmat, Fin.rev] at e
    exact (mul_eq_zero.1 (by linear_combination e : 2 * ρ g 0 1 = 0)).resolve_left h2
  have := zero_of_trace ρ hs (Matrix.single 1 0 1) fun g => by simp [Matrix.trace_mul_single, h1]
  simpa using congrFun (congrFun this 1) 0

theorem UpperTheory.V.Fr.of_trace :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [Field K] [IsAlgClosed K] [Algebra C K], Function.Injective (algebraMap C K) → ∀ (r : F.G0 →* Matrix (Fin n) (Fin n) K) (t : F.G0 → C) (χ : ∀ v, Fin n → F.Gv v →* Cˣ), IsTr (O := O) (F := F) (n := n) t → (∀ g, algebraMap C K (t g) = (r g).trace) → (∀ g, t (F.star g) = t g) → IsPsi (O := O) (F := F) (n := n) (fun v i g => (χ v i g : C)) → (∀ v g h, (r h * ordProd (fun s => r (F.loc0 v s)) (fun i s => algebraMap C K (χ v i s)) g).trace = 0) → ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (φ : C →+* K') (ρ' : NRep F n K'), MatIrr ⊤ ρ'.r → (∀ g, φ (t g) = (ρ'.r g).trace) → ∃ (ρ : NRep F n K) (h : GL (Fin n) K), (∀ g, ρ.r g = h * r g * h⁻¹) ∧ (∀ v i g, (ρ.ψ v i g : K) = algebraMap C K (χ v i g)) ∧ Integral (O := O) C ρ ∧ MatIrr ⊤ ρ.r := by
  intro l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ _ hinj r t χ ht htr hst hχ hord K' _ _ φ ρ' hirr hφ
  obtain ⟨ss, sm, -, -, -⟩ := UpperTheory.V.Fr.star hF
  have h2C : IsUnit (2 : C) := by
    by_contra hn2
    have h0 := (res_eq_zero_iff O C 2).2 hn2
    rw [map_ofNat] at h0
    have := (CharP.cast_eq_zero_iff (ResidueField O) l 2).1 (by exact_mod_cast h0)
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have h2K : (2 : K) ≠ 0 := by simpa [map_ofNat] using (h2C.map (algebraMap C K)).ne_zero
  have h2K' : (2 : K') ≠ 0 := by simpa [map_ofNat] using (h2C.map φ).ne_zero
  have hs' : Submodule.span K' (Set.range ρ'.r) = ⊤ :=
    (UpperTheory.V.AlgebraTools.Det.irrIffSpan ρ'.r).1 fun N hN => hirr N fun g _ => hN g
  have hs := span_of_trace (algebraMap C K) hinj φ t r ρ'.r htr hφ hs'
  have s1 : F.star 1 = 1 := by simp [Frame.star]
  let r' : F.G0 →* Matrix (Fin n) (Fin n) K :=
    { toFun := fun g => (r (F.star g))ᵀ
      map_one' := by rw [s1, map_one, Matrix.transpose_one]
      map_mul' := fun g h => by rw [sm, map_mul, Matrix.transpose_mul] }
  obtain ⟨P, hP, hPr⟩ := conj_of_trace r' r hs fun g => by
    show (r (F.star g))ᵀ.trace = _
    rw [Matrix.trace_transpose, ← htr, ← htr, hst]
  replace hPr : ∀ g, (r (F.star g))ᵀ * P = P * r g := hPr
  have sc : ∀ g, F.star g * F.conj g = 1 := fun g => by rw [Frame.star, ← map_mul, inv_mul_cancel, map_one]
  have hform : ∀ g, (r g)ᵀ * P * r (F.conj g) = P := fun g => by
    have := hPr (F.star g)
    rw [ss] at this
    rw [this, Matrix.mul_assoc, ← map_mul, sc, map_one, Matrix.mul_one]
  have cc : ∀ g, F.conj (F.conj g) = g := fun g => by
    have := ss g
    simpa only [Frame.star, map_inv, inv_inv] using this
  have hsym : Pᵀ = P := by
    refine (UpperTheory.V.AlgebraTools.Det.signLemma r F.conj (fun _ => 1) P hs cc (fun _ => rfl) hP
      fun g => by rw [hform, one_smul]).resolve_right fun ha => ?_
    rcases hn with rfl | rfl
    · refine not_alt h2K' ρ'.r hs' fun g x => ?_
      rw [← ρ'.pol, ← map_mul, ← map_mul, ← hφ, ← hφ, ← hφ, ← hφ, ← map_add (f := _), ← map_mul]
      congr 1
      apply hinj
      rw [map_add (f := _), map_mul, htr, htr, htr, htr, map_mul, map_mul, ← Matrix.trace_add, ← Matrix.mul_add,
        alt_two h2K P _ _ hP ha (hPr g), Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
    · have hd := congrArg Matrix.det ha
      rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hd
      exact mul_ne_zero h2K ((Matrix.isUnit_iff_isUnit_det _).1 hP).ne_zero (by linear_combination hd)
  obtain ⟨ρ, h, h1, h2, h3⟩ := UpperTheory.V.Fr.of_form hF hn C K hinj r P t χ hP hsym hform ht htr hχ
    fun v g => zero_of_trace r hs _ (hord v g)
  refine ⟨ρ, h, h1, h2, h3, fun N hN => ?_⟩
  refine (UpperTheory.V.AlgebraTools.Det.irrIffSpan ρ.r).2 ?_ N fun g => hN g trivial
  refine span_of_trace (algebraMap C K) hinj φ t ρ.r ρ'.r (fun g => ?_) hφ hs'
  rw [h1, htr, Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCocv
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_gl {C : Type} [CommRing C] {n : ℕ} (a b c : GL (Fin n) C)
    (ha : UpT (a : Matrix (Fin n) (Fin n) C)) (hb : UpT (b : Matrix (Fin n) (Fin n) C))
    (hc : UpT (c : Matrix (Fin n) (Fin n) C)) :
    UpT (((a * b * c⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) - 1) := by
  have ha' : (a : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => ha i j h
  have hb' : (b : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hb i j h
  have hc' : (c : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hc i j h
  letI : Invertible (c : Matrix (Fin n) (Fin n) C) := c.invertible
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hc'
  rw [← Matrix.coe_units_inv] at hi
  intro i j h
  have h1 := ((ha'.mul hb').mul hi) (show id j < id i from h)
  rw [Matrix.sub_apply, Units.val_mul, Units.val_mul, h1, Matrix.one_apply_ne (ne_of_gt h), sub_zero]

private theorem ring_id {R : Type} [Ring R] (o c x a w : R) (h : (1 + o) * (1 + c) = (1 + x) * (1 + a) * (1 + w))
    (h1 : o * c = 0) (h2 : x * a = 0) (h3 : x * w = 0) (h4 : a * w = 0) : o - (x - c + a) = w := by
  have e1 : (1 + o) * (1 + c) = 1 + o + c + o * c := by noncomm_ring
  have e2 : (1 + x) * (1 + a) * (1 + w) = 1 + x + a + w + x * a + x * w + a * w + x * a * w := by noncomm_ring
  rw [e1, e2, h1, h2, h3, h4] at h
  simp only [add_zero, zero_mul] at h
  have : o = 1 + x + a + w - c - 1 := by rw [← h]; abel
  rw [this]; abel

theorem UpperTheory.V.Fr.pr_cocv :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → ∀ v s t, (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) ∈ (B.bar O).b v := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D u hK v s t
  obtain ⟨hom, ha, -, -⟩ := pr_omk hF O C' C p B D hK
  have hle : RingHom.ker p ≤ maximalIdeal C' := fun x hx => by
    rw [← res_eq_zero_iff O, ← res_map p, (RingHom.mem_ker).1 hx, map_zero]
  have ev := pr_evk O C' n (RingHom.ker p) u hK hle
  have hdel : ∀ s, F.del (F.loc v s) = 1 := fun s => (F.loc0 v s).2
  have hright : ∀ s, (B.r (F.loc v s)).right = 1 := fun s => (B.nu _).trans (hdel s)
  have hres : ∀ x : GL (Fin n) C', GeneralLinearGroup.map (res O C : C →+* ResidueField O)
      (GeneralLinearGroup.map (p : C' →+* C) x) = GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x := by
    intro x
    ext i j
    exact res_map p _
  have hval : ∀ x : GL (Fin n) C', (x : Matrix (Fin n) (Fin n) C').map (res O C') =
      ((GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x : GL (Fin n) (ResidueField O)) :
        Matrix (Fin n) (Fin n) (ResidueField O)) := fun x => rfl

  set T : Matrix (Fin n) (Fin n) C' :=
    ((D.t v s * D.t v t * (D.t v (s * t))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1 with hT
  have hTup : UpT T := upT_gl _ _ _ (D.t_tri v s) (D.t_tri v t) (D.t_tri v _)
  have hTK : ∀ i j, T i j ∈ RingHom.ker p := by
    have e : GeneralLinearGroup.map (p : C' →+* C) (D.t v s * D.t v t * (D.t v (s * t))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, D.t_map, D.t_map, D.t_map, map_mul, map_mul, SemidirectProduct.mul_left,
        hright, sgnAct_one]
      group
    intro i j
    have e2 := congrArg (fun x : GL (Fin n) C => (x : Matrix (Fin n) (Fin n) C) i j) e
    rw [RingHom.mem_ker, hT, Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 (Eq.trans e2 ?_)
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  set gi : Matrix (Fin n) (Fin n) C' := (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hgi
  set g : Matrix (Fin n) (Fin n) C' := ((D.g v : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hg
  set ri : Matrix (Fin n) (Fin n) C' := (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hri
  set r : Matrix (Fin n) (Fin n) C' := ((D.r (F.loc v s) : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hr
  have hW1 : ∀ i j, (gi * T) i j ∈ RingHom.ker p := fun i j => (((ev T hTK).2.1 gi).1 i j).1
  have hW : ∀ i j, (gi * T * g) i j ∈ RingHom.ker p := fun i j => (((ev _ hW1).2.1 g).1 i j).2
  have hX1 : ∀ i j, (r * D.a v t) i j ∈ RingHom.ker p := fun i j => (((ev _ (ha v t)).2.1 r).1 i j).1
  have hX : ∀ i j, (r * D.a v t * ri) i j ∈ RingHom.ker p := fun i j => (((ev _ hX1).2.1 ri).1 i j).2
  have key : D.om (F.loc v s, F.loc v t) - (r * D.a v t * ri - D.a v (s * t) + D.a v s) = gi * T * g := by
    refine ring_id _ _ _ _ _ ?_ ((ev _ (hom _)).1 _ (ha v _)).1 ((ev _ hX).1 _ (ha v _)).1
      ((ev _ hX).1 _ hW).1 ((ev _ (ha v _)).1 _ hW).1
    have e1 : 1 + r * D.a v t * ri = ((D.r (F.loc v s) * (D.r (F.loc v t) * ((D.g v)⁻¹ * D.t v t * D.g v)⁻¹) *
        (D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') := by
      rw [SetLift.a, mul_sub, sub_mul, mul_one, hr, hri, Units.mul_inv, add_sub_cancel]
      rfl
    have e2 : 1 + gi * T * g = (((D.g v)⁻¹ * (D.t v s * D.t v t * (D.t v (s * t))⁻¹) * D.g v : GL (Fin n) C') :
        Matrix (Fin n) (Fin n) C') := by
      rw [hT, mul_sub, sub_mul, mul_one, hg, hgi, Units.inv_mul, add_sub_cancel]
      rfl
    rw [e1, e2]
    simp only [SetLift.om, SetLift.a, add_sub_cancel, hdel, sgnAct_one, ← Units.val_mul, map_mul]
    congr 1
    group
  have hXc : ∀ i j, (r * D.a v t * ri - D.a v (s * t)) i j ∈ RingHom.ker p := fun i j =>
    sub_mem (hX i j) (ha v _ i j)
  have hXca : ∀ i j, (r * D.a v t * ri - D.a v (s * t) + D.a v s) i j ∈ RingHom.ker p := fun i j =>
    add_mem (hXc i j) (ha v _ i j)
  have k2 := congrArg (fun M : Matrix (Fin n) (Fin n) C' => M.map (evK (RingHom.ker p) u)) key
  rw [((ev _ (hom _)).1 _ hXca).2.2, ((ev _ hXc).1 _ (ha v _)).2.1, ((ev _ hX).1 _ (ha v _)).2.2,
    ((ev _ hX1).2.1 ri).2.2, ((ev _ (ha v t)).2.1 r).2.1, ((ev _ hW1).2.1 g).2.2, ((ev _ hTK).2.1 gi).2.1,
    hr, hri, hg, hgi, hval, hval, hval, hval, map_inv, map_inv, ← hres, ← hres (D.g v), D.r_map, D.g_map] at k2
  have k3 : (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) =
      ((((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O)) *
        T.map (evK (RingHom.ker p) u) * ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) := by
    refine Eq.trans ?_ k2
    have e : ((B.bar O).ad.comp (F.loc v)) s ((D.co u).2 v t) =
        ((B.bar O).r (F.loc v s)).adFun ((D.a v t).map (evK (RingHom.ker p) u)) := rfl
    have e' : ((B.bar O).r (F.loc v s)).right = 1 := hright s
    simp only [dOne]
    rw [e, GG.adFun, if_pos e', add_sub_assoc, add_comm]
    rfl
  rw [k3]
  intro i j h
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
    Matrix.mul_one, Matrix.map_apply, hTup i j h, evK_of_mem u (zero_mem _)]
  exact map_zero u
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCorrect
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C} (hM : UpT M) (hN : UpT N) :
    UpT (M * N) := fun i j h => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hM i c hc, zero_mul]
  · rw [hN c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

theorem UpperTheory.V.Fr.pr_correct :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (μ : ResidueField O →+ C'), IsSq O μ → (∀ c, p (μ c) = 0) → ∀ (β : F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) (Y : F.V → Matrix (Fin n) (Fin n) (ResidueField O)) (a : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) (ResidueField O)), IsLocallyConstant β → (∀ x, D.om x = (dOne (B.bar O).ad β x).map μ) → (∀ v s, D.a v s = (a v s).map μ) → (∀ v s, a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v)) ∈ (B.bar O).b v) → ∃ B' : Box F n C', B'.Cont (maximalIdeal C') ∧ B'.map (p : C' →+* C) = B ∧ ∀ s, (B'.r s).mat = (1 - (β s).map μ) * (D.r s : Matrix (Fin n) (Fin n) C') := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D μ hμ hpμ β Y a hβ hom ha hb
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := pr_sqz O C' n μ hμ
  have hres : ∀ z : C', res O C (p z) = res O C' z := fun z => res_map p z
  let x : F.Γ → GG (m := n) (R := C') := fun s => SemidirectProduct.mk (D.r s) (F.del s)
  have hK1 : ∀ s, GG.map (res O C' : C' →+* ResidueField O) (x s) = (B.bar O).r s := by
    intro s
    apply SemidirectProduct.ext
    · ext i j
      simp [x, GG.map, Box.map, hres, ← D.r_map s]
    · simp [x, GG.map, Box.map, B.nu]
  have hdl : ∀ v (s : F.Gv v), F.del (F.loc v s) = 1 := fun v s => MonoidHom.mem_ker.1 (F.loc0 v s).2
  have hAd : ∀ v (s : F.Gv v) M, (B.bar O).ad (F.loc v s) M =
      (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C') * M *
        (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v s M
    show GG.adFun ((B.bar O).r (F.loc v s)) M = _
    rw [← hK1]
    clear hom ha hb he5 he4 he3 he2 he1 hβ hpμ hμ
    simp [GG.adFun, GG.mat, GG.map, x, hdl]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.coe_units_inv]
    calc (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') *
          (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C')
        = ((((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') *
            (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C')).map (res O C') :=
          (Matrix.map_mul (f := (res O C').toRingHom)).symm
      _ = 1 := by
          rw [Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
  have hxmul : ∀ s t, x s * x t = GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
    intro s t
    have hu : D.r s * sgnAct (m := n) (R := C') (F.del s) (D.r t) * (D.r (s * t))⁻¹ = e (dOne (B.bar O).ad β (s, t)) := by
      apply Units.ext
      rw [he1, ← hom (s, t)]
      simp [SetLift.om]
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, ← hu]
      simp [x]
    · simp [x]
  have hcomm : ∀ s X, x s * GG.ofGL (e X) = GG.ofGL (e ((B.bar O).ad s X)) * x s := by
    intro s X
    rw [he5 (x s) X, hK1 s]
    rfl
  let R' : F.Γ → GG (m := n) (R := C') := fun s => GG.ofGL (e (-β s)) * x s
  have hmul : ∀ s t, R' (s * t) = R' s * R' t := by
    intro s t
    symm
    calc R' s * R' t = GG.ofGL (e (-β s)) * (x s * GG.ofGL (e (-β t))) * x t := by
          simp only [R', mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) * (x s * x t) := by
          rw [hcomm]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) *
            GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [hxmul]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s + (B.bar O).ad s (-β t) + dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [he2, he2, map_mul, map_mul]
      _ = R' (s * t) := by
          simp only [R']
          congr 3
          simp only [dOne, map_neg]
          abel
  let rr : F.Γ →* GG (m := n) (R := C') := MonoidHom.mk' R' hmul
  have hneg : ∀ Z : Matrix (Fin n) (Fin n) (ResidueField O), (-Z).map μ = -(Z.map μ) := by
    intro Z
    ext i j
    simp
  have hpe : ∀ X, GeneralLinearGroup.map (p : C' →+* C) (e X) = 1 := by
    intro X
    ext i j
    simp only [GeneralLinearGroup.map_apply, he1, Matrix.add_apply, Matrix.map_apply, Units.val_one, map_add (f := _)]
    have h0 : (p : C' →+* C) (μ (X i j)) = 0 := hpμ _
    rw [h0, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hconj : ∀ (A : GL (Fin n) C') X, A * e X * A⁻¹ =
      e ((A : Matrix (Fin n) (Fin n) C').map (res O C') * X * ((A⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
    intro A X
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he1, he1, mul_add, mul_one, add_mul, Units.mul_inv, (he4 _ X).1, (he4 _ _).2]
  have hGbar : ∀ v, ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) =
        (D.g v : Matrix (Fin n) (Fin n) C').map (res O C') ∧
      (((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) =
        (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v
    constructor
    · ext i j
      simp [Box.map, ← D.g_map v, hres]
    · ext i j
      simp [Box.map, ← D.g_map v, hres, ← map_inv]
  refine ⟨{ r := rr, nu := ?_, g := fun v => D.g v * e (-(Y v)), tri := ?_ }, ?_, ?_, ?_⟩
  · intro s
    show (GG.ofGL (e (-β s)) * x s).right = F.del s
    simp [x]
  · intro v s
    show UpT ((↑(D.g v * e (-(Y v))) : Matrix (Fin n) (Fin n) C') * (R' (F.loc v s)).mat *
      (((D.g v * e (-(Y v)))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C'))
    have hr : D.r (F.loc v s) = e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v) := by
      rw [← mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [he1, ← ha v s]
      simp [SetLift.a]
    have hmat : (R' (F.loc v s)).mat = ↑(e (-β (F.loc v s)) * D.r (F.loc v s)) := by
      simp [R', GG.mat, x]
    have h1 : D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹ = e ((B.bar O).ad (F.loc v s) (Y v)) := by
      rw [hconj, hAd]
    have hX : e (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) =
        e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s) := by
      rw [← he2, ← he2, ← he2]
      congr 1
      abel
    have key : D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹ =
        e ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) * D.t v s := by
      rw [← hconj, hX]
      calc D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹
          = D.g v * e (-(Y v)) * e (-β (F.loc v s)) *
              (D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹) * D.r (F.loc v s) * (D.g v)⁻¹ := by
            rw [_root_.mul_inv_rev, he3, neg_neg]
            group
        _ = D.g v * e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) *
              (e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v)) * (D.g v)⁻¹ := by
            rw [h1, ← hr]
        _ = D.g v * (e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s)) *
              (D.g v)⁻¹ * D.t v s := by
            group
    have hW : UpT ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
      rw [← (hGbar v).1, ← (hGbar v).2]
      exact hb v s
    rw [hmat, ← Units.val_mul, ← Units.val_mul, key, Units.val_mul, he1]
    apply upT_mul _ (D.t_tri v s)
    intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.map_apply, hW i j hij, map_zero, add_zero]
  · intro i j N
    have hB : IsLocallyConstant fun s =>
        (D.r s : Matrix (Fin n) (Fin n) C').map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro s0
      have hall : ∀ᶠ s in nhds s0, ∀ a b,
          Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s : Matrix (Fin n) (Fin n) C') a b) =
            Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s0 : Matrix (Fin n) (Fin n) C') a b) :=
        Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
          (IsLocallyConstant.iff_eventually_eq _).1 (D.r_cont a b N) s0
      filter_upwards [hall] with s hs
      ext a b
      exact hs a b
    have hA := hβ.comp (fun Z =>
      ((1 : Matrix (Fin n) (Fin n) C') + (-Z).map μ).map (Ideal.Quotient.mk (maximalIdeal C' ^ N)))
    have hM := (IsLocallyConstant.comp₂ hA hB (· * ·)).comp (fun M => M i j)
    convert hM using 1
    funext s
    change Ideal.Quotient.mk (maximalIdeal C' ^ N) ((R' s).mat i j) =
      (((1 + (-β s).map μ).map (Ideal.Quotient.mk (maximalIdeal C' ^ N))) *
        (D.r s : Matrix (Fin n) (Fin n) C').map (Ideal.Quotient.mk (maximalIdeal C' ^ N))) i j
    rw [← Matrix.map_mul, Matrix.map_apply]
    congr 1
    show (R' s).mat i j = _
    simp [R', GG.mat, x, he1]
  · apply Box.ext
    · apply MonoidHom.ext
      intro s
      apply SemidirectProduct.ext
      · show GeneralLinearGroup.map (p : C' →+* C) (R' s).left = (B.r s).left
        simp [R', x, hpe, D.r_map]
      · show (R' s).right = (B.r s).right
        simp [R', x, B.nu]
    · funext v
      show GeneralLinearGroup.map (p : C' →+* C) (D.g v * e (-(Y v))) = B.g v
      rw [map_mul, hpe, mul_one, D.g_map]
  · intro s
    show (R' s).mat = _
    simp [R', GG.mat, x, he1, hneg, sub_eq_add_neg]
end

