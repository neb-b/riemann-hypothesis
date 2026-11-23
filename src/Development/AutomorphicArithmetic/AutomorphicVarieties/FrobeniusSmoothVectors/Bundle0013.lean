module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgFamily
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_family :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsVertexRing C 𝔪 → IsModel O C 𝔪 ρ → ∃ f : ∀ N : ℕ, S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1), (∀ N, S.ρ.map (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ρ.map (Ideal.Quotient.mk (𝔪 ^ (N + 1)))) ∧ (∀ N x d, Ideal.Quotient.mk (𝔪 ^ (N + 1 + 1)) d = f (N + 1) x → Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N x) ∧ ∀ N, ∀ x ∈ maximalIdeal S.R ^ (N + 1), f N x = 0 := by
  intro l _ O _ _ F n S C _ _ _ D _ _ _ _ 𝔪 ρ hV hM
  choose hco hmax using alg_quot O C 𝔪 hV
  have hex : ∀ N, ∃! f : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1),
      S.ρ.map (f : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ρ.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) := by
    intro N
    letI := hco N
    exact S.univ _ _ (alg_lift C 𝔪 ρ hM _ (Ideal.Quotient.mkₐ O (𝔪 ^ (N + 1))) (fun x hx => by
      rw [hmax N]
      exact Ideal.mem_map_of_mem _ hx))
  choose f hf huniq using hex
  refine ⟨f, hf, ?_, ?_⟩
  · intro N x d hd
    have hle : 𝔪 ^ (N + 1 + 1) ≤ 𝔪 ^ (N + 1) := Ideal.pow_le_pow_right (Nat.le_succ _)
    have hcomp : (Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) = f N := by
      apply huniq N
      have e : (((Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) :
          S.R →+* D ⧸ 𝔪 ^ (N + 1)) =
          ((Ideal.Quotient.factorₐ O hle : D ⧸ 𝔪 ^ (N + 1 + 1) →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) :
            D ⧸ 𝔪 ^ (N + 1 + 1) →+* D ⧸ 𝔪 ^ (N + 1)).comp (f (N + 1) : S.R →+* D ⧸ 𝔪 ^ (N + 1 + 1)) := rfl
      rw [e, ← NRep.map_map, hf (N + 1), NRep.map_map]
      rfl
    rw [← hcomp, AlgHom.comp_apply, ← hd]
    rfl
  · intro N x hx
    letI := hco N
    have hm : ∀ y ∈ maximalIdeal S.R,
        f N y ∈ Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪 := by
      intro y hy
      rw [← hmax N, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hy
    have hle : Ideal.map (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) (maximalIdeal S.R) ≤
        Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪 := by
      rw [Ideal.map_le_iff_le_comap]
      exact hm
    have hx' := Ideal.mem_map_of_mem (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) hx
    rw [Ideal.map_pow] at hx'
    have h2 := Ideal.pow_right_mono hle (N + 1) hx'
    rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot] at h2
    exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgLau
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private noncomputable def UpperTheory.V.Fr.lauT (K : Type) [CommRing K] : Multiplicative ℤ →* (AddMonoidAlgebra K ℤ)ˣ :=
  (AddMonoidAlgebra.of K ℤ).toHomUnits

private theorem UpperTheory.V.Fr.lauT_zpow (K : Type) [CommRing K] (m : ℤ) :
    ((lauT K (Multiplicative.ofAdd 1) ^ m : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) =
      AddMonoidAlgebra.single m 1 := by
  rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
  rfl

theorem UpperTheory.V.Fr.alg_lau :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → ∃ ρD : NRep F n (lauSub (ρ.part C)), (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) ∧ (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hc
  obtain ⟨χ, -, hχ⟩ := hc.psi
  obtain ⟨ρ', hr, hψ⟩ := alg_twist (lauT K (Multiplicative.ofAdd 1))
    (NRep.map (AddMonoidAlgebra.singleZeroRingHom : K →+* AddMonoidAlgebra K ℤ) ρ)
  have hr' : ∀ g i j, ρ'.r g i j = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j) := by
    intro g i j
    rw [hr, lauT_zpow, NRep.map_r]
    simp [AddMonoidAlgebra.single_mul_single]
  have hψ' : ∀ v i g, ((ρ'.ψ v i g : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) =
      AddMonoidAlgebra.single 0 (ρ.ψ v i g : K) := by
    intro v i g
    rw [hψ]
    rfl
  have h1 : ∀ g i j, ρ'.r g i j ∈ lauSub (ρ.part C) := by
    intro g i j
    rw [hr']
    exact single_mem_lauSub _ (NRep.r_mem_part C ρ g i j)
  have h2 : ∀ v i g, ((ρ'.ψ v i g : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) ∈
      lauSub (ρ.part C) := by
    intro v i g
    rw [hψ']
    apply single_mem_lauSub
    rw [← hχ, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  exact ⟨NRep.restrict ρ' (lauSub (ρ.part C)) h1 h2, fun g i j => hr' g i j,
    fun v i g => hψ' v i g⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgModel
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prod_single {K α : Type} [CommRing K] (d : α → ℤ) (a : α → K) (L : List α) :
    (L.map fun s => AddMonoidAlgebra.single (d s) (a s)).prod =
      AddMonoidAlgebra.single (L.map d).sum (L.map a).prod := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, ih, AddMonoidAlgebra.single_mul_single, List.map_cons,
      List.map_cons, List.sum_cons, List.prod_cons]

private theorem alg_val {C K : Type} [CommRing C] [CommRing K] [Algebra C K] (P : ℤ → Submodule C K)
    [SetLike.GradedMonoid P] (c : C) :
    (algebraMap C (lauSub P) c).1 = AddMonoidAlgebra.single 0 (algebraMap C K c) := by
  rfl

private theorem w_ne_w_of_ne (n : ℕ) {i j : Fin n} (hij : i ≠ j) : w n i ≠ w n j := by
  intro h
  apply hij
  unfold w at h
  split_ifs at h <;> exact Fin.ext (by omega)

theorem UpperTheory.V.Fr.alg_model :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → ∀ (h : HasVertex (ρ.part C)) (ρD : NRep F n (lauSub (ρ.part C))), (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) → (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) → IsModel O C (vertex h) ρD := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hc h ρD hr hψ
  have key : ∀ (c : C) (y : K), algebraMap C K c = y → ∀ p : lauSub (ρ.part C),
      p.1 = AddMonoidAlgebra.single 0 y → algebraMap C (lauSub (ρ.part C)) c = p := by
    intro c y hcy p hp
    apply Subtype.ext
    rw [alg_val, hp, hcy]
  refine ⟨alg_cont C ρ hc h ρD hr hψ, ?_, ?_, ?_, ?_⟩
  · intro g i j hij
    rw [mem_vertex]
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    rw [hr, map_zero]
    have hne : (0 : ℤ) ≠ w n i - w n j := by
      intro h0
      exact w_ne_w_of_ne n hij (by omega)
    exact (Finsupp.single_eq_of_ne hne).symm
  · intro g i
    obtain ⟨c, hc1, hc2⟩ := hc.dg g i
    refine ⟨c, key c _ hc1 _ ?_, hc2⟩
    rw [hr, sub_self]
  · intro v i g
    obtain ⟨χ, hχ, hχψ⟩ := hc.psi
    exact ⟨χ v i g, key _ _ (hχψ v i g) _ (hψ v i g), (hχ v i).2 g⟩
  · intro x hx
    obtain ⟨L, hL, rfl⟩ := hx
    have hmem : (L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod ∈ ρ.part C 0 :=
      Submodule.subset_span ⟨L, hL, rfl⟩
    obtain ⟨c, hc'⟩ := h.zero _ hmem
    refine ⟨c, key c _ hc' _ ?_⟩
    have e1 : ∀ L' : List (F.G0 × Fin n × Fin n),
        ((L'.map fun s => ρD.r s.1 s.2.1 s.2.2).prod : lauSub (ρ.part C)).1 =
          (L'.map fun s => AddMonoidAlgebra.single (w n s.2.1 - w n s.2.2) (ρ.r s.1 s.2.1 s.2.2)).prod := by
      intro L'
      induction L' with
      | nil => rfl
      | cons s L' ih =>
        rw [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih, hr, List.map_cons, List.prod_cons]
    rw [e1, prod_single (fun s : F.G0 × Fin n × Fin n => w n s.2.1 - w n s.2.2)
      (fun s => ρ.r s.1 s.2.1 s.2.2) L, hL]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgSep
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_sep :
    ∀ {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K] {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P), IsNoetherianRing (lauSub P) → ⨅ N : ℕ, vertex h ^ N = ⊥ := by
  intro C K _ _ _ _ P _ h hN
  classical
  rw [eq_bot_iff]
  intro p hp
  rw [Submodule.mem_iInf] at hp
  let comp : lauSub P → ℤ → lauSub P := fun x j =>
    ⟨AddMonoidAlgebra.single j (x.1.coeff j), single_mem_lauSub P (x.2 j)⟩
  have coeff_comp (x : lauSub P) (j : ℤ) :
      (comp x j).1 = AddMonoidAlgebra.single j (x.1.coeff j) := rfl
  have comp_mem_vertex : ∀ x : lauSub P, x ∈ vertex h → ∀ j, comp x j ∈ vertex h := by
    intro x hx j
    change ∃ c ∈ maximalIdeal C, algebraMap C K c = (comp x j).1.coeff 0
    rw [coeff_comp, AddMonoidAlgebra.coeff_single]
    by_cases hj : j = 0
    · subst j
      rw [Finsupp.single_eq_same]
      exact hx
    · exact ⟨0, Ideal.zero_mem _, by rw [Finsupp.single_eq_of_ne' hj, map_zero]⟩
  have comp_mem_pow : ∀ (N : ℕ) (x : lauSub P), x ∈ vertex h ^ N →
      ∀ j, comp x j ∈ vertex h ^ N := by
    intro N
    induction N with
    | zero =>
      intro x hx j
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on (C := fun z => ∀ j, comp z j ∈ vertex h ^ (n + 1)) hx ?_ ?_
      · intro y hy z hz j
        have e : comp (y * z) j =
            ∑ i ∈ y.1.coeff.support, comp y i * comp z (-i + j) := by
          apply Subtype.ext
          simp only [AddSubmonoidClass.coe_finsetSum, coeff_comp, Subalgebra.coe_mul,
            AddMonoidAlgebra.single_mul_single, add_neg_cancel_left]
          rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
          exact map_sum (AddMonoidAlgebra.singleAddHom j) _ _
        rw [e, pow_succ]
        exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (ih y hy i) (comp_mem_vertex z hz _)
      · intro y z hy hz j
        have e : comp (y + z) j = comp y j + comp z j := by
          apply Subtype.ext
          simp only [coeff_comp, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
            AddMonoidAlgebra.single_add]
        rw [e]
        exact add_mem (hy j) (hz j)
  have hcomp : ∀ j : ℤ, (p : AddMonoidAlgebra K ℤ).coeff j = 0 := by
    intro j
    let a := (p : AddMonoidAlgebra K ℤ).coeff j
    let q := comp p j
    have hq : ∀ N : ℕ, q ∈ vertex h ^ N := fun N => comp_mem_pow N p (hp N) j
    have hq' : q ∈ ⨅ i : ℕ, (vertex h) ^ i • (⊤ : Submodule (lauSub P) (lauSub P)) := by
      rw [Submodule.mem_iInf]
      intro i
      simp only [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hq i
    obtain ⟨⟨r, hr⟩, hrq⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (vertex h) q).1 hq'
    have hrq' : r * q = q := hrq
    obtain ⟨c, hc, hcr⟩ := hr
    have h1 : ((r * q : lauSub P) : AddMonoidAlgebra K ℤ).coeff j =
        (r : AddMonoidAlgebra K ℤ).coeff 0 * a := by
      have h0 := AddMonoidAlgebra.coeff_mul_single_add (r : AddMonoidAlgebra K ℤ) a j 0
      rw [zero_add] at h0
      exact h0
    have h2 : ((r * q : lauSub P) : AddMonoidAlgebra K ℤ).coeff j = a := by
      rw [hrq']
      show (AddMonoidAlgebra.single j a).coeff j = a
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    rw [h2, ← hcr] at h1
    have hu : IsUnit (algebraMap C K (1 - c)) :=
      (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits c hc).map _
    have h3 : algebraMap C K (1 - c) * a = 0 := by
      rw [map_sub, map_one, sub_mul, one_mul, ← h1, sub_self]
    exact hu.mul_right_eq_zero.1 h3
  apply Subtype.ext
  ext j
  simpa using hcomp j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.BorelProjectionIsTwoCocycle
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem grp_id {H : Type*} [Group H] (a b c ab bc abc : H) :
    (a * b * ab⁻¹) * (ab * c * abc⁻¹) = (a * (b * c * bc⁻¹) * a⁻¹) * (a * bc * abc⁻¹) := by
  group

theorem UpperTheory.V.Fr.borelProjection_isTwoCocycle :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → ∀ s t r, (B.bar O).ad s ((D.co u).1 (t, r)) + (D.co u).1 (s, t * r) = (D.co u).1 (s * t, r) + (D.co u).1 (s, t) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D u hK s t r
  have hKm : RingHom.ker p ≤ maximalIdeal C' := by
    intro y hy
    rw [← res_eq_zero_iff O C', ← res_map p y, RingHom.mem_ker.mp hy, map_zero]
  obtain ⟨hom, -, -, -⟩ := pr_omk hF O C' C p B D hK
  obtain ⟨x, hx⟩ : ∃ x : F.Γ → GG (m := n) (R := C'), ∀ a, x a = ⟨D.r a, F.del a⟩ := ⟨_, fun _ => rfl⟩
  have hW : ∀ a b, x a * x b * (x (a * b))⁻¹ =
      GG.ofGL (D.r a * sgnAct n C' (F.del a) (D.r b) * (D.r (a * b))⁻¹) := by
    intro a b
    rw [hx, hx, hx]
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
        SemidirectProduct.inv_right, SemidirectProduct.left_inl, GG.ofGL]
      rw [← MulAut.mul_apply, ← map_mul, map_mul F.del a b, mul_inv_cancel, map_one, MulAut.one_apply]
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, SemidirectProduct.right_inl,
        GG.ofGL, map_mul, mul_inv_cancel, mul_one]
  have hz : ∀ a b, ((D.r a * sgnAct n C' (F.del a) (D.r b) * (D.r (a * b))⁻¹ : GL (Fin n) C') :
      Matrix (Fin n) (Fin n) C') = 1 + D.om (a, b) := by
    intro a b
    simp [SetLift.om]
  have hbar : (B.bar O).r s = GG.map (res O C' : C' →+* ResidueField O) (x s) := by
    rw [hx]
    apply SemidirectProduct.ext
    · ext i j
      simp [Box.map, GG.map, ← D.r_map s, res_map]
    · simp [Box.map, GG.map, B.nu]
  have key : ∀ a b : GG (m := n) (R := C'), a.right = 1 → (a * b).mat = a.mat * b.mat := by
    intro a b ha
    simp only [GG.mat, SemidirectProduct.mul_left, ha, map_one, MulAut.one_apply, Units.val_mul]
  have hofr : ∀ w : GL (Fin n) C', (GG.ofGL w).right = 1 := fun w => rfl
  have hmat : ∀ w : GL (Fin n) C', (GG.ofGL w).mat = (w : Matrix (Fin n) (Fin n) C') := fun w => rfl
  have hW' : x s * x (t * r) * (x (s * t * r))⁻¹ =
      GG.ofGL (D.r s * sgnAct n C' (F.del s) (D.r (t * r)) * (D.r (s * (t * r)))⁻¹) := by
    rw [mul_assoc s t r]
    exact hW s (t * r)
  have h := grp_id (x s) (x t) (x r) (x (s * t)) (x (t * r)) (x (s * t * r))
  rw [hW s t, hW (s * t) r, hW t r, hW'] at h
  have hyr : (x s * GG.ofGL (D.r t * sgnAct n C' (F.del t) (D.r r) * (D.r (t * r))⁻¹) * (x s)⁻¹).right
      = 1 := by
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, GG.ofGL,
      SemidirectProduct.right_inl, mul_one, mul_inv_cancel]
  have hM := congrArg GG.mat h
  rw [key _ _ (hofr _), key _ _ hyr, hmat, hmat, hmat] at hM
  obtain ⟨-, -, hE3⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm (D.om (t, r)) (hom (t, r))
  obtain ⟨hAK, hAmap, hconj⟩ := hE3 (x s)
  rw [hconj _ (hz t r), hz s t, hz (s * t) r, hz s (t * r)] at hM
  obtain ⟨h1, -, -⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm (D.om (s, t)) (hom (s, t))
  obtain ⟨h12, h12add, -⟩ := h1 (D.om (s * t, r)) (hom _)
  obtain ⟨hA, -, -⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm ((x s).adFun (D.om (t, r))) hAK
  obtain ⟨hA4, hA4add, -⟩ := hA (D.om (s, t * r)) (hom _)
  have hsum : D.om (s, t) + D.om (s * t, r) = (x s).adFun (D.om (t, r)) + D.om (s, t * r) := by
    have e1 : (1 + D.om (s, t)) * (1 + D.om (s * t, r)) = 1 + (D.om (s, t) + D.om (s * t, r)) := by
      rw [add_mul, one_mul, mul_add, mul_one, h12]
      abel
    have e2 : (1 + (x s).adFun (D.om (t, r))) * (1 + D.om (s, t * r)) =
        1 + ((x s).adFun (D.om (t, r)) + D.om (s, t * r)) := by
      rw [add_mul, one_mul, mul_add, mul_one, hA4]
      abel
    rw [e1, e2] at hM
    exact add_left_cancel hM
  change ((B.bar O).r s).adFun ((D.om (t, r)).map (evK (RingHom.ker p) u)) +
      (D.om (s, t * r)).map (evK (RingHom.ker p) u) =
      (D.om (s * t, r)).map (evK (RingHom.ker p) u) + (D.om (s, t)).map (evK (RingHom.ker p) u)
  rw [hbar, ← hAmap, ← hA4add, add_comm ((D.om (s * t, r)).map _), ← h12add, hsum]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CwZero
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem cw_skew {K : Type} [CommRing K] (x : GG (m := 3) (R := K)) (hx : x * x = 1) (hr : x.right = -1)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : x.adFun X = X) :
    (X * x.mat * Jmat (R := K) 3)ᵀ = -(X * x.mat * Jmat (R := K) 3) := by
  have h1 : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left hx
    simpa [hr, sgnAct_neg_one] using this
  have hX' : x.mat * thetaLie X * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = X := by
    simpa [GG.adFun, hr] using hX
  have h2 : (theta x.left)⁻¹ = x.left := inv_eq_of_mul_eq_one_left h1
  have hg : x.mat = Jmat (R := K) 3 * x.matᵀ * Jmat (R := K) 3 := by
    show ((x.left : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    conv_lhs => rw [← h2]
    rw [theta_inv_val]
    rfl
  have hgJ : x.mat * Jmat (R := K) 3 = Jmat (R := K) 3 * x.matᵀ := by
    conv_lhs => rw [hg]
    rw [Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]
  have hXg : X * x.mat = x.mat * thetaLie X := by
    conv_lhs => rw [← hX']
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    have : ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x.mat = 1 := by
      show ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (x.left : Matrix (Fin 3) (Fin 3) K) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.mul_one]
  calc (X * x.mat * Jmat (R := K) 3)ᵀ = Jmat (R := K) 3 * x.matᵀ * Xᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Jmat_transpose, Matrix.mul_assoc]
    _ = x.mat * Jmat (R := K) 3 * Xᵀ := by rw [hgJ]
    _ = -(X * x.mat * Jmat (R := K) 3) := by
        rw [hXg, thetaLie]
        simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]

private theorem cw_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (x : GG (m := 3) (R := K)) (hx : x * x = 1) (hr : x.right = -1)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : x.adFun X = X) (a : (X * x.mat) 0 0 = 0) (b : (X * x.mat) 0 1 = 0)
    (c : (X * x.mat) 1 0 = 0) : X = 0 := by
  have hs := cw_skew x hx hr X hX
  have e : ∀ i j, (X * x.mat * Jmat (R := K) 3) i j = (X * x.mat) i (Fin.rev j) := by
    intro i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat]
  have sk : ∀ i j, (X * x.mat * Jmat (R := K) 3) j i = -(X * x.mat * Jmat (R := K) 3) i j := by
    intro i j
    have := congrFun (congrFun hs i) j
    simpa [Matrix.transpose_apply] using this
  have dg : ∀ i, (X * x.mat * Jmat (R := K) 3) i i = 0 := by
    intro i
    have h := sk i i
    have h' : (2 : K) * (X * x.mat * Jmat (R := K) 3) i i = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
    exact (mul_eq_zero.mp h').resolve_left h2
  have m01 : (X * x.mat * Jmat (R := K) 3) 0 1 = 0 := by rw [e]; exact b
  have m02 : (X * x.mat * Jmat (R := K) 3) 0 2 = 0 := by rw [e]; exact a
  have m12 : (X * x.mat * Jmat (R := K) 3) 1 2 = 0 := by rw [e]; exact c
  have m10 : (X * x.mat * Jmat (R := K) 3) 1 0 = 0 := by rw [sk, m01, neg_zero]
  have m20 : (X * x.mat * Jmat (R := K) 3) 2 0 = 0 := by rw [sk, m02, neg_zero]
  have m21 : (X * x.mat * Jmat (R := K) 3) 2 1 = 0 := by rw [sk, m12, neg_zero]
  have hM : X * x.mat * Jmat (R := K) 3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.zero_apply]
    all_goals first
      | exact dg _
      | exact m01
      | exact m02
      | exact m12
      | exact m10
      | exact m20
      | exact m21
  have hY : X * x.mat = 0 := by
    have : X * x.mat = X * x.mat * Jmat (R := K) 3 * Jmat (R := K) 3 := by
      rw [Matrix.mul_assoc (X * x.mat), Jmat_mul_Jmat, Matrix.mul_one]
    rw [this, hM, Matrix.zero_mul]
  have hinv : x.mat * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    show (x.left : Matrix (Fin 3) (Fin 3) K) * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc X = X * x.mat * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = 0 := by rw [hY, Matrix.zero_mul]

theorem UpperTheory.V.Fr.ep_cw :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), ∀ c : F.Γ, c * c = 1 → F.del c = -1 → Module.finrank K (LinearMap.ker (h.ad 0 c - 1)) ≤ 1 ∧ Module.finrank K (LinearMap.ker (h.ad 1 c - 1)) ≤ 2 := by
  intro l _ k _ F K _ h2 B π h c hc hd
  have hx : B.r c * B.r c = 1 := by rw [← map_mul, hc, map_one]
  have hr : (B.r c).right = -1 := by rw [B.nu, hd]
  have hg : ∀ a b, pw a b ≠ 0 → (B.r c).mat a b = 0 := fun a b hab => h.r c a b hab
  have key : ∀ j (v : LinearMap.ker (h.ad j c - 1)),
      (B.r c).adFun ((v : adp K j) : Matrix (Fin 3) (Fin 3) K) = ((v : adp K j) : Matrix (Fin 3) (Fin 3) K) := by
    intro j v
    have hv := v.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
    have := congrArg Subtype.val hv
    simpa [Box.Ev.ad, Box.ad, adRep, GG.ad_apply] using this
  constructor
  · let f : LinearMap.ker (h.ad 0 c - 1) →ₗ[K] K :=
      { toFun := fun v => (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0
        map_add' := by intro v w; simp [Matrix.add_mul]
        map_smul' := by intro a v; simp [Matrix.smul_mul] }
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hX : ∀ a b, pw a b ≠ 0 → ((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) a b = 0 :=
        fun a b hab => (v : adp K 0).2 a b hab
      have e01 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hg 0 1 (by decide), hX 0 1 (by decide), hg 2 1 (by decide)]
        ring
      have e10 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hX 1 0 (by decide), hg 1 0 (by decide), hX 1 2 (by decide)]
        ring
      have h0 := cw_zero h2 (B.r c) hx hr _ (key 0 v) hv e01 e10
      exact Subtype.ext (Subtype.ext h0)
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
  · let f : LinearMap.ker (h.ad 1 c - 1) →ₗ[K] K × K :=
      { toFun := fun v => ((((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1,
          (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0)
        map_add' := by intro v w; simp [Matrix.add_mul]
        map_smul' := by intro a v; simp [Matrix.smul_mul] }
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hX : ∀ a b, pw a b ≠ 1 → ((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) a b = 0 :=
        fun a b hab => (v : adp K 1).2 a b hab
      have e00 : (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hX 0 0 (by decide), hg 1 0 (by decide), hX 0 2 (by decide)]
        ring
      have hv' := Prod.mk.inj hv
      have h0 := cw_zero h2 (B.r c) hx hr _ (key 1 v) e00 hv'.1 hv'.2
      exact Subtype.ext (Subtype.ext h0)
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
end

