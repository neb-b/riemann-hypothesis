module

public import Development.EtaleCohomology.TateTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0004
public import Development.EtaleCohomology.TateTwists.Bundle0002

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.CupflipAwExistsPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_aw_cochain : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ γ : Cochain ((chains R).obj E) K k, μ.IsAW hk α β γ

def cupflip_aw_leibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
    (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)),
    μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ →
      δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂

theorem ev_zero_cochain {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  simp [ev]

theorem isAW_zero_left {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ}
    (hk : n + m = k) (β : Cochain ((chains R).obj E) J m) : μ.IsAW hk 0 β 0 := by
  intro N w h U x
  simp [ev_zero_cochain]

theorem isAW_zero_right {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ}
    (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) : μ.IsAW hk α 0 0 := by
  intro N w h U x
  simp [ev_zero_cochain]

theorem cupflip_aw_exists_of (hc : cupflip_aw_cochain) (hl : cupflip_aw_leibniz) : cupflip_aw_exists := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hc R μ E hk α.1 β.1
  have hα : δ n (n + 1) α.1 = 0 := Cocycle.δ_eq_zero α (n + 1)
  have hβ : δ m (m + 1) β.1 = 0 := Cocycle.δ_eq_zero β (m + 1)
  have h1 : μ.IsAW (by omega) (δ n (n + 1) α.1) β.1 (0 : Cochain ((chains R).obj E) K (k + 1)) := by
    rw [hα]; exact isAW_zero_left μ _ β.1
  have h2 : μ.IsAW (by omega) α.1 (δ m (m + 1) β.1) (0 : Cochain ((chains R).obj E) K (k + 1)) := by
    rw [hβ]; exact isAW_zero_right μ _ α.1
  have hδ : δ k (k + 1) γ = 0 := by
    rw [hl R μ hk α.1 β.1 γ 0 0 hγ h1 h2]; simp
  exact ⟨Cocycle.mk γ (k + 1) rfl hδ, hγ⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.CupflipAwFlipPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def CupflipSteen (h : ∀ N, Pr N →₀ ℤ) : Prop :=
  (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧
    ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1)

def cupflip_steen : Prop := ∃ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h

def cupflip_homotopy : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (hk' : m + n = k)
      (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → ν.IsAW hk' β.1 α.1 γ'.1 →
        ∃ η : Cochain ((chains R).obj E) K (k - 1), δ (k - 1) k η = γ.1 - (n * m).negOnePow • γ'.1

theorem cupflip_aw_flip_of (hst : cupflip_steen) (hho : cupflip_homotopy) : cupflip_aw_flip := by
  intro R _ I J K μ ν hflip E n m k h h' α β γ γ' hγ hγ'
  obtain ⟨s, hs⟩ := hst
  obtain ⟨η, hη⟩ := hho s hs R μ ν hflip E h h' α β γ γ' hγ hγ'
  rcases Int.units_eq_one_or ((n * m).negOnePow) with he | he
  · rw [he, one_smul] at hη ⊢
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (k - 1) (by omega)]
    exact ⟨η, hη⟩
  · rw [he, Units.neg_smul, one_smul] at hη ⊢
    rw [← sub_eq_zero, sub_neg_eq_add, ← CohomologyClass.mk_add, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (k - 1) (by omega)]
    exact ⟨η, by rw [hη, sub_neg_eq_add]; rfl⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.CupflipWdPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_wd_aw : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
    (∀ α β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β γ' → γ = γ') ∧
    (∀ α α' β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ α β β' γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ'))

def cupflip_wd_cobdry : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k),
    μ.IsAW hk α.1 β.1 γ.1 → (α ∈ coboundaries _ _ n ∨ β ∈ coboundaries _ _ m) → γ ∈ coboundaries _ _ k

theorem cupflip_wd_of (ha : cupflip_wd_aw) (hb : cupflip_wd_cobdry) : cupflip_wd := by
  intro R _ I J K μ E n m k hk
  classical
  obtain ⟨hex, huniq, haddl, haddr⟩ := ha R μ E hk
  let aw : Cocycle ((chains R).obj E) I n → Cocycle ((chains R).obj E) J m → Cocycle ((chains R).obj E) K k :=
    fun α β => Classical.choose (hex α β)
  have haw : ∀ α β, μ.IsAW hk α.1 β.1 (aw α β).1 := fun α β => Classical.choose_spec (hex α β)
  have heq : ∀ α β γ, μ.IsAW hk α.1 β.1 γ.1 → aw α β = γ := fun α β γ h =>
    Subtype.ext (huniq _ _ _ _ (haw α β) h)
  have addl : ∀ α α' β, aw (α + α') β = aw α β + aw α' β := fun α α' β =>
    heq _ _ _ (haddl _ _ _ _ _ (haw α β) (haw α' β))
  have addr : ∀ α β β', aw α (β + β') = aw α β + aw α β' := fun α β β' =>
    heq _ _ _ (haddr _ _ _ _ _ (haw α β) (haw α β'))
  let g : Cocycle ((chains R).obj E) I n →
      CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
    fun α => CohomologyClass.descAddMonoidHom
      (AddMonoidHom.mk' (fun β => CohomologyClass.mk (aw α β))
        (fun β β' => by simp only [addr, CohomologyClass.mk_add]))
      (fun β hβ => by
        rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, CohomologyClass.mk_eq_zero_iff]
        exact hb R μ E hk α β _ (haw α β) (Or.inr hβ))
  have gmk : ∀ α β, g α (CohomologyClass.mk β) = CohomologyClass.mk (aw α β) := fun _ _ => rfl
  have gadd : ∀ α α', g (α + α') = g α + g α' := by
    intro α α'
    refine AddMonoidHom.ext fun b => ?_
    obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
    rw [AddMonoidHom.add_apply, gmk, gmk, gmk, addl, CohomologyClass.mk_add]
  let c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
      CohomologyClass ((chains R).obj E) K k :=
    CohomologyClass.descAddMonoidHom (AddMonoidHom.mk' g gadd) (fun α hα => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
      refine AddMonoidHom.ext fun b => ?_
      obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
      rw [gmk, AddMonoidHom.zero_apply, CohomologyClass.mk_eq_zero_iff]
      exact hb R μ E hk α β _ (haw α β) (Or.inl hα))
  refine ⟨c, fun α β γ h => ?_⟩
  change g α (CohomologyClass.mk β) = _
  rw [gmk, heq α β γ h]

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.CyclotomicPrimitiveRootProductIdentitiesOfAdjoin
section
open Polynomial Finset GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.PrimPf

noncomputable def μ (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

lemma hμ (q : ℕ) [NeZero q] : IsPrimitiveRoot (μ q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma aeval_cyc {n : ℕ} (hn : 0 < n) {ν : ℂ} (h : IsPrimitiveRoot ν n) :
    aeval ν (cyclotomic n ℤ) = 0 := by
  rw [cyclotomic_eq_minpoly h hn]; exact minpoly.aeval _ _

lemma hom_aeval {S T : Type} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (f : S →+* T) (x : S) (p : ℤ[X]) :
    f (aeval x p) = aeval (f x) p := by
  rw [aeval_def, aeval_def, hom_eval₂]; congr 1; exact RingHom.ext_int _ _

abbrev R (q : ℕ) := AdjoinRoot (cyclotomic q ℤ)

noncomputable abbrev θ (q : ℕ) : R q := AdjoinRoot.root (cyclotomic q ℤ)

noncomputable def φ (q : ℕ) [NeZero q] : R q →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℤ ℂ) (μ q) (by rw [← aeval_def]; exact aeval_cyc (NeZero.pos q) (hμ q))

lemma φ_root (q : ℕ) [NeZero q] : φ q (θ q) = μ q := AdjoinRoot.lift_root _

lemma φ_inj (q : ℕ) [NeZero q] : Function.Injective (φ q) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [AdjoinRoot.mk_eq_zero]
  have h : aeval (μ q) p = 0 := by
    rw [φ, AdjoinRoot.lift_mk] at hx; rwa [aeval_def]
  rw [cyclotomic_eq_minpoly (hμ q) (NeZero.pos q)]
  exact minpoly.isIntegrallyClosed_dvd ((hμ q).isIntegral (NeZero.pos q)) h

noncomputable def ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : R q →+* A :=
  AdjoinRoot.lift (algebraMap ℤ A) ζ.1 (by rw [← aeval_def]; exact ζ.2.2)

lemma ψ_root {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ψ ζ (θ q) = ζ.1 :=
  AdjoinRoot.lift_root _

lemma θ_pow (q : ℕ) [NeZero q] : θ q ^ q = 1 :=
  φ_inj q (by rw [map_pow, φ_root, map_one, (hμ q).pow_eq_one])

lemma root_of_prim {q r a : ℕ} [NeZero q] (hr : 0 < r) (h : IsPrimitiveRoot (μ q ^ a) r) :
    aeval (θ q ^ a) (cyclotomic r ℤ) = 0 :=
  φ_inj q (by rw [hom_aeval (φ q), map_pow, φ_root, map_zero]; exact aeval_cyc hr h)

lemma image_range (q : ℕ) [NeZero q] :
    (range q).image (fun a => μ q ^ a) = nthRootsFinset q (1 : ℂ) := by
  ext x
  rw [mem_image, mem_nthRootsFinset (NeZero.pos q)]
  constructor
  · rintro ⟨a, -, rfl⟩; rw [← pow_mul, mul_comm, pow_mul, (hμ q).pow_eq_one, one_pow]
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx
    exact ⟨i, mem_range.2 hi, rfl⟩

lemma image_prim (q : ℕ) [NeZero q] :
    ((range q).filter (fun a => Nat.Coprime a q)).image (fun a => μ q ^ a) = primitiveRoots q ℂ := by
  ext x
  rw [mem_image, mem_primitiveRoots (NeZero.pos q)]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact (hμ q).pow_of_coprime a (mem_filter.1 ha).2
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx.pow_eq_one
    exact ⟨i, mem_filter.2 ⟨mem_range.2 hi, ((hμ q).pow_iff_coprime (NeZero.pos q) i).1 hx⟩, rfl⟩

lemma inj_on (q : ℕ) [NeZero q] (s : Finset ℕ) (hs : s ⊆ range q) :
    Set.InjOn (fun a => μ q ^ a) s := by
  intro i hi j hj h
  exact (hμ q).pow_inj (mem_range.1 (hs hi)) (mem_range.1 (hs hj)) h

lemma C_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (μ q ^ a)) = (X ^ q - 1 : ℂ[X]) := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos q) (hμ q), ← image_range,
    prod_image (inj_on q _ subset_rfl)]

lemma C_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (μ q ^ a)) = cyclotomic q ℂ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (hμ q), ← image_prim,
    prod_image (inj_on q _ (filter_subset _ _))]

lemma mapφ_C_prod (q : ℕ) [NeZero q] (s : Finset ℕ) :
    (∏ a ∈ s, (X - C (θ q ^ a))).map (φ q) = ∏ a ∈ s, (X - C (μ q ^ a)) := by
  simp [Polynomial.map_prod, φ_root]

lemma R_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (θ q ^ a)) = (X ^ q - 1 : (R q)[X]) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_all]; simp

lemma R_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (θ q ^ a))
      = (cyclotomic q ℤ).map (algebraMap ℤ (R q)) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_prim, Polynomial.map_map, ← map_cyclotomic_int]
  congr 1; exact RingHom.ext_int _ _

lemma C_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (μ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : ℂ[X]) := by
  have h := C_prod_all (n + 1)
  rw [prod_range_succ', pow_zero, ← geom_sum_mul, C_1] at h
  have hne : (X - 1 : ℂ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℂ)
  exact mul_right_cancel₀ hne h

lemma R_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (θ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : (R (n + 1))[X]) := by
  apply Polynomial.map_injective _ (φ_inj (n + 1))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, map_pow, φ_root, Polynomial.map_pow]
  simpa using C_prod_geom n

lemma eval_prod_ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) (f : ℕ → ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ f a))) = ∏ a ∈ s, (y - ζ.1 ^ f a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma eval_prod_ψ0 {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ a))) = ∏ a ∈ s, (y - ζ.1 ^ a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma unit_prod {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ i ∈ range (q - 1), (1 - ζ.1 ^ (i + 1)) = (q : A) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos q)).symm⟩
  have h := congrArg (eval₂ (ψ ζ) 1) (R_prod_geom n)
  rw [eval_prod_ψ ζ 1 _ (fun i => i + 1)] at h
  simpa [eval₂_finsetSum] using h

theorem cyclotomic_primitive_root_product_identities_of_adjoin_root : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  intro q _ A _
  have hq1 : ∀ ζ : Prim q A, ζ.1 ^ q = 1 := fun ζ => by
    rw [← ψ_root, ← map_pow, θ_pow, map_one]
  have hu : ∀ ζ : Prim q A, IsUnit ζ.1 := fun ζ =>
    IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) (by
      rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q), hq1])
  have hmod : ∀ (ζ : Prim q A) (a : ℕ), ζ.1 ^ a = ζ.1 ^ (a % q) := fun ζ a => by
    conv_lhs => rw [← Nat.mod_add_div a q, pow_add, pow_mul, hq1, one_pow, mul_one]
  have hlt : ∀ (ζ : Prim q A) (c d : ℕ), c < d → d < q → IsUnit (ζ.1 ^ c - ζ.1 ^ d) := by
    intro ζ c d hcd hd
    obtain ⟨i, rfl⟩ : ∃ i, d = c + (i + 1) := ⟨d - c - 1, by omega⟩
    have e : ζ.1 ^ c - ζ.1 ^ (c + (i + 1)) = ζ.1 ^ c * (1 - ζ.1 ^ (i + 1)) := by ring
    rw [e]
    refine ((hu ζ).pow c).mul (isUnit_of_dvd_unit ?_ ζ.2.1)
    have hd := dvd_prod_of_mem (fun j => 1 - ζ.1 ^ (j + 1)) (mem_range.2 (show i < q - 1 by omega))
    rw [unit_prod ζ] at hd
    exact hd
  refine ⟨hq1, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ a ha
    refine ⟨⟨ζ.1 ^ a, ζ.2.1, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim (NeZero.pos q) ((hμ q).pow_of_coprime a ha), map_zero]
  · intro ζ a b hab
    rw [hmod ζ a, hmod ζ b]
    have hne : a % q ≠ b % q := hab
    have ha := Nat.mod_lt a (NeZero.pos q)
    have hb := Nat.mod_lt b (NeZero.pos q)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt ζ _ _ h hb
    · have := (hlt ζ _ _ h ha).neg
      rwa [neg_sub] at this
  · intro ζ x hx
    have h := congrArg (eval₂ (ψ ζ) x) (R_prod_all q)
    rw [eval_prod_ψ0] at h
    simpa [hx] using h
  · intro ζ ξ
    have h := congrArg (eval₂ (ψ ζ) ξ.1) (R_prod_prim q)
    rw [eval_prod_ψ0, eval₂_map] at h
    rw [h]
    have e : (ψ ζ).comp (algebraMap ℤ (R q)) = algebraMap ℤ A := RingHom.ext_int _ _
    rw [e, ← aeval_def]; exact ξ.2.2
  · intro r hr ζ
    have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr (NeZero.pos q)
    have hur : IsUnit (r : A) := by
      obtain ⟨k, hk⟩ := hr
      have := ζ.2.1
      rw [hk, Nat.cast_mul] at this
      exact isUnit_of_mul_isUnit_left this
    refine ⟨⟨ζ.1 ^ (q / r), hur, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim hr0 ((hμ q).pow (NeZero.pos q) (Nat.div_mul_cancel hr).symm), map_zero]

end LateralTheory.EtaleFoundations.PrimPf
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ConerveIsomorphism

variable {T : Type 1} [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ)
  {U V : T} (g : U ⟶ V)

noncomputable def phi (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ⟶
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) :=
  WidePullback.lift (Ψ.map (WidePushout.head _)).unop (fun j => (Ψ.map (WidePushout.ι _ j)).unop)
    (fun j => by
      have h := WidePushout.arrow_ι (fun _ : Fin (n+1) => g) j
      rw [← unop_comp, ← Ψ.map_comp, h])

lemma phi_π (n : ℕ) (j : Fin (n+1)) :
    phi Ψ g n ≫ WidePullback.π _ j = (Ψ.map (WidePushout.ι _ j)).unop := by
  unfold phi; erw [WidePullback.lift_π]

lemma phi_base (n : ℕ) :
    phi Ψ g n ≫ WidePullback.base _ = (Ψ.map (WidePushout.head _)).unop := by
  unfold phi; erw [WidePullback.lift_base]

lemma aux (n : ℕ) (j : Fin (n+1)) :
    Ψ.map g ≫ (WidePullback.π (fun _ : Fin (n+1) => (Ψ.map g).unop) j).op =
      (WidePullback.base (fun _ : Fin (n+1) => (Ψ.map g).unop)).op := by
  rw [← WidePullback.π_arrow (fun _ : Fin (n+1) => (Ψ.map g).unop) j]
  rfl

noncomputable def cocone (n : ℕ) : Cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g) ⋙ Ψ) where
  pt := op (widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop))
  ι :=
    { app := fun j => match j with
        | none => (WidePullback.base _).op
        | some j => (WidePullback.π _ j).op
      naturality := by
        rintro X Y (_ | j)
        · rw [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
            Category.id_comp, Category.comp_id]
        · exact (aux Ψ g n j).trans (Category.comp_id _).symm }

lemma natural (a b : ℕ) (σ : Fin (a+1) → Fin (b+1)) :
    (Ψ.map (WidePushout.desc (WidePushout.head (fun _ : Fin (b+1) => g))
      (fun i => WidePushout.ι (fun _ : Fin (b+1) => g) (σ i))
      (fun i => WidePushout.arrow_ι (fun _ : Fin (b+1) => g) (σ i)))).unop ≫ phi Ψ g a =
    phi Ψ g b ≫ WidePullback.lift (WidePullback.base (fun _ : Fin (b+1) => (Ψ.map g).unop))
      (fun i => WidePullback.π (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i))
      (fun i => WidePullback.π_arrow (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i)) := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, Category.assoc, phi_π, WidePullback.lift_π, phi_π, ← unop_comp, ← Ψ.map_comp,
      WidePushout.ι_desc]
  · rw [Category.assoc, Category.assoc, phi_base, WidePullback.lift_base, phi_base, ← unop_comp,
      ← Ψ.map_comp, WidePushout.head_desc]

variable (hΨ : ∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ)

noncomputable def hc (n : ℕ) :
    IsColimit (Ψ.mapCocone (colimit.cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g)))) :=
  haveI := hΨ n
  isColimitOfPreserves Ψ (colimit.isColimit _)

noncomputable def psi (n : ℕ) :
    widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) ⟶
      (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop :=
  ((hc Ψ g hΨ n).desc (cocone Ψ g n)).unop

lemma desc_phi (n : ℕ) : (hc Ψ g hΨ n).desc (cocone Ψ g n) ≫ (phi Ψ g n).op = 𝟙 _ := by
  apply (hc Ψ g hΨ n).hom_ext
  rintro (_ | j)
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)).trans (Quiver.Hom.unop_inj (phi_base Ψ g n)))
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))).trans (Quiver.Hom.unop_inj (phi_π Ψ g n j)))

noncomputable def levelIso (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ≅
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) where
  hom := phi Ψ g n
  inv := psi Ψ g hΨ n
  hom_inv_id := congrArg Quiver.Hom.unop (desc_phi Ψ g hΨ n)
  inv_hom_id := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, phi_π, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))
    · rw [Category.assoc, phi_base, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)

end LateralTheory.EtaleFoundations.ConerveIsomorphism

open LateralTheory.EtaleFoundations.ConerveIsomorphism in
theorem LateralTheory.EtaleFoundations.etale_cech_conerve_image_iso_cech_nerve_of_preserves_wide_pushouts : LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts := by
  intro T _ _ Ψ hΨ U V g
  refine ⟨NatIso.ofComponents (fun n => levelIso Ψ g hΨ n.unop.len) ?_, ?_⟩
  · intro m n h
    exact natural Ψ g _ _ h.unop.toOrderHom
  · ext n : 1
    exact (phi_base Ψ g (unop n).len).symm
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy : Prop :=
  ∀ (R : Type) [CommRing R] (K L I : Cx R) [I.IsKInjective] (f : K ⟶ L) [QuasiIso f],
    (∀ a : K ⟶ I, ∃ m : L ⟶ I, Nonempty (Homotopy (f ≫ m) a)) ∧
    ∀ m m' : L ⟶ I, Nonempty (Homotopy (f ≫ m) (f ≫ m')) → Nonempty (Homotopy m m')

def LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (I : Cx R) [I.IsStrictlyGE 0] (a b : sgl F ⟶ I),
    Nonempty (Homotopy a b) → a = b

theorem LateralTheory.EtaleFoundations.etale_sheaf_ext_hom_injective_resolution_of_lift_and_rigidity (hA : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy)
    (hB : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual) : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso := by
  intro R _ F T I _ _ ε _
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m, hm⟩ := (hA R (sgl F) T I ε).1 a
    exact ⟨m, hB R F I _ _ hm⟩
  · exact (hA R (sgl F) T I ε).2 m m' ⟨Homotopy.ofEq h⟩
end

