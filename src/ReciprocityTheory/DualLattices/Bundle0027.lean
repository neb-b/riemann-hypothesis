module

public import ReciprocityTheory.DualLattices.Bundle0021
public import ReciprocityTheory.DualLattices.PowMemCarrier
public import ReciprocityTheory.DualLattices.Bundle0024

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.EigenLiftsFrobenius
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section FrobA

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

private theorem hasLen_of_linearEquiv {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {x : NNReal} (e : M ≃ₗ[R] M') (h : HasLen v R M' x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨φ⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans φ⟩, hx⟩

lemma coefX_int (D : Lifts H U X) (hdet : (valM D).det ≠ 0)
    (hbasis : H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val))
    {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    ∃ r : Nb p g → R, coefX D f = algebraMap R C ∘ r := by
  rw [hbasis] at hf
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  refine ⟨r, ?_⟩
  have hfv : f = valM D *ᵥ (algebraMap R C ∘ r) := by
    rw [← hr]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, valM, Matrix.of_apply,
      Function.comp_apply, monX, xL, Algebra.smul_def]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  rw [coefX, hfv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

lemma xL_pow_mem (D : Lifts H U X) (hp : 2 ≤ p) (j : Ix g) :
    (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) := by
  have hx : xL D j ∈ augIdeal H.AA.carrier := D.x_mem j
  have hxA : xL D j ∈ H.AA.carrier := hx.1
  have hx0 : xL D j 0 = 0 := hx.2
  have hpow : ∀ n : ℕ, xL D j ^ (n + 1) ∈ augIdeal H.AA.carrier := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
        exact H.AA.mul_mem _ _ ih.1 hxA
      · show (xL D j ^ (n + 1 + 1)) 0 = 0
        rw [Pi.pow_apply, hx0, zero_pow (by omega)]
  have heq : (fun y => xL D j y ^ p) = xL D j * xL D j ^ (p - 1 - 1 + 1) := by
    funext y
    rw [Pi.mul_apply, Pi.pow_apply, ← pow_succ']
    congr 1
    omega
  rw [heq]
  exact Submodule.subset_span ⟨_, hx, _, hpow _, rfl⟩

def blockEquiv (D : Lifts H U X) (τ : Fin U.m) :
    blockL D τ ≃ₗ[R] ({l // D.κ l = τ} → R) where
  toFun c l := c.1 l.1
  invFun d := ⟨fun k => if h : D.κ k = τ then d ⟨k, h⟩ else 0, fun k hk => by simp [hk]⟩
  left_inv c := by
    apply Subtype.ext
    funext k
    by_cases h : D.κ k = τ
    · simp [h]
    · simp [h, c.2 k h]
  right_inv d := by funext l; simp [l.2]
  map_add' c c' := rfl
  map_smul' r c := rfl

end FrobA

theorem frob_of (h1 : LiftMonomialDeterminantStatement) (h2 : FrobeniusBlockStatement) (h3 : FrobeniusLengthBoundStatement) :
    EigenLiftsFrobeniusStatement := by
  unfold EigenLiftsFrobeniusStatement
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hbasis i
  have hv := hS.integers
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdet := h1 p g C v R O σ cp hS H U X D
  obtain ⟨h2a, h2b⟩ := h2 p g C v R O σ cp hp2 hS H U X D
  have hsq : sqIdeal (augIdeal H.AA.carrier) ≤ H.AA.carrier := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, f', hf', rfl⟩
    exact H.AA.mul_mem _ _ hf.1 hf'.1
  have hfS : ∀ j, (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) :=
    fun j => xL_pow_mem D hp j
  have hrex : ∀ j : Ix g, ∃ r : Nb p g → R,
      coefX D (fun y => xL D j y ^ p) = algebraMap R C ∘ r :=
    fun j => coefX_int D hdet hbasis (hsq (hfS j))
  choose r hr using hrex
  let c : Ix g → Ix g → R := fun j k => if D.κ k = U.φ i then r j (Pi.single k 1) else 0
  have hc : ∀ j, D.κ j = i → ∀ k, algebraMap R C (c j k) = linX D (fun y => xL D j y ^ p) k := by
    intro j hj k
    by_cases hk : D.κ k = U.φ i
    · simp only [c, if_pos hk, linX, hr j, Function.comp_apply]
    · simp only [c, if_neg hk, map_zero]
      exact (h2a j k (by rw [hj]; exact hk)).symm
  have hcard : Fintype.card {j // D.κ j = i} = Fintype.card {l // D.κ l = U.φ i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, D.card_phi i]
  let e'' : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i} := Fintype.equivOfCardEq hcard
  let eτ : {l // D.κ l = U.φ i} ≃ Fin (Fintype.card {l // D.κ l = U.φ i}) := Fintype.equivFin _
  let σE : Fin (Fintype.card {l // D.κ l = U.φ i}) ≃ {j // D.κ j = i} := eτ.symm.trans e''.symm
  let Y : Matrix (Fin (Fintype.card {l // D.κ l = U.φ i})) (Fin (Fintype.card {l // D.κ l = U.φ i})) R :=
    fun a b => c (σE b).1 (eτ.symm a).1
  let Ψ : blockL D (U.φ i) ≃ₗ[R] (Fin (Fintype.card {l // D.κ l = U.φ i}) → R) :=
    (blockEquiv D (U.φ i)).trans (LinearEquiv.funCongrLeft R R eτ.symm)
  let N : Submodule R (Ix g → R) :=
    ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map (blockL D (U.φ i)).subtype
  have hcomap : N.comap (blockL D (U.φ i)).subtype = (LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap :=
    Submodule.comap_map_eq_of_injective (blockL D (U.φ i)).injective_subtype _
  have hmapΨ : ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map Ψ.toLinearMap = LinearMap.range Y.mulVecLin :=
    Submodule.map_comap_eq_of_surjective Ψ.surjective _
  have hlen : HasLen v R (blockL D (U.φ i) ⧸ N.comap (blockL D (U.φ i)).subtype)
      (v (algebraMap R C Y.det)) := by
    rw [hcomap]
    exact hasLen_of_linearEquiv (Submodule.Quotient.equiv _ _ Ψ hmapΨ) (Smith.hasLen_coker_det hv Y)
  have hNle : N ≤ blockL D (U.φ i) := Submodule.map_subtype_le _ _
  have hreal : ∀ x ∈ N, ∃ f ∈ sqIdeal (augIdeal H.AA.carrier),
      ∀ k, algebraMap R C (x k) = linX D f k := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hy)
    refine ⟨∑ b, w b • (fun t => xL D (σE b).1 t ^ p),
      Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hfS _), ?_⟩
    intro k
    have hyΨ : y = Ψ.symm (Y.mulVecLin w) := by rw [hw]; exact (Ψ.symm_apply_apply y).symm
    have hyk : (y : Ix g → R) k = ∑ b, c (σE b).1 k * w b := by
      rw [hyΨ]
      by_cases h : D.κ k = U.φ i
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dite_eq_left h]
        show ∑ b, Y (eτ ⟨k, h⟩) b * w b = _
        simp only [Y, Equiv.symm_apply_apply]
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dite_eq_right h]
        simp [c, h]
    show algebraMap R C ((y : Ix g → R) k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hyk, map_sum]
    simp only [linX, coefX, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← algebraMap_smul C (w b), Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul,
      mul_comm]
    congr 1
    exact hc (σE b).1 (σE b).2 k
  have hYdet : v (algebraMap R C Y.det) = X i ^ p / X (U.φ i) := by
    rw [RingHom.map_det]
    have hYZ : (algebraMap R C).mapMatrix Y = (Matrix.of fun j l : {j // D.κ j = i} =>
        linX D (fun y => xL D j.1 y ^ p) (e'' l).1)ᵀ.submatrix σE σE := by
      ext a b
      show algebraMap R C (c (σE b).1 (eτ.symm a).1) =
        linX D (fun y => xL D (σE b).1 y ^ p) (e'' (σE a)).1
      rw [hc (σE b).1 (σE b).2]
      simp [σE]
    rw [hYZ, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact h2b i e''
  have hz := h3 p g C v R O σ cp hp2 hS H U X D hdet hbasis (U.φ i) N _ hNle hreal hlen
  rw [hYdet] at hz
  have hXne : X (U.φ i) ≠ 0 := by
    rw [← D.ε_prod (U.φ i)]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      (Valuation.ne_zero_iff v).mpr ((map_ne_zero_iff _ hinj).mpr (D.ε_ne j))
  rw [div_le_iff₀ (pos_iff_ne_zero.mpr hXne)] at hz
  exact hz.trans_eq (mul_comm _ _)

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.NsmulKerZero
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace ATower

variable {p : ℕ} (Tw : ATower R₀ p)

lemma ξmul_surj (n : ℕ) : Function.Surjective (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) := by
  rintro ⟨k, hk⟩
  have hk' : k ∈ Ideal.span {Tw.ξ n} := by
    rw [← Tw.ker_eq n]
    simpa using hk
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hk'
  refine ⟨a, Subtype.ext ?_⟩
  show Tw.ξ n * a = k
  rw [← ha, mul_comm]

lemma exists_factor (n : ℕ) : ∃ g' : (Tw.π n).ker →ₗ[R₀] (Tw.R n : Type u),
    g' ∘ₗ ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) = (Tw.π n).1.toLinearMap := by
  have hle : LinearMap.ker (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) ≤
      LinearMap.ker (Tw.π n).1.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : Tw.ξ n * a = 0 := congrArg Subtype.val ha
    have hm : a ∈ Ideal.span {Tw.ξ n} := Tw.ann n a (by rw [mul_comm]; exact h0)
    rw [← Tw.ker_eq n, RingHom.mem_ker] at hm
    exact hm
  have hs := Tw.ξmul_surj n
  refine ⟨(LinearMap.ker _).liftQ _ hle ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _ hs).symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun a => ?_
  have h1 : (LinearMap.quotKerEquivOfSurjective _ hs).symm (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) a) =
      Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]

end ATower

namespace BX

variable (B : BX R₀) {p : ℕ}

lemma nsmul_ker_zero (Tw : ATower R₀ p) (n : ℕ) (V : B.gg ⊗[R₀] (Tw.π n).ker) :
    (p ^ (n + 1)) • V = 0 := by
  have hc : ((p : (Tw.R' n : Type u))) ^ (n + 1) = 0 := by exact_mod_cast Tw.char n
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul g k =>
    have hk : (p ^ (n + 1)) • k = 0 := by
      apply Subtype.ext
      simp [nsmul_eq_mul, hc]
    rw [← TensorProduct.tmul_smul, hk, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

lemma exists_lift (Tw : ATower R₀ p) (n : ℕ) (y : B.G (Tw.R n)) (hy : (p ^ (n + 1)) • y = 0) :
    ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)), B.map (Tw.π n) th = y ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) := by
  obtain ⟨th, hth⟩ := B.surj (Tw.π n) (Tw.sqZero n) y
  have h0 : B.map (Tw.π n) ((p ^ (n + 1)) • th) = 0 := by rw [map_nsmul, hth, hy]
  obtain ⟨v, hv⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 h0
  obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective B.gg (Tw.ξmul_surj n) v
  exact ⟨th, w, hth, by rw [← hv, ← hw]; rfl⟩

lemma lift_indep (Tw : ATower R₀ p) (n : ℕ) (th th' : B.G (Tw.R' n)) (w w' : B.gg ⊗[R₀] (Tw.R' n : Type u))
    (he : B.map (Tw.π n) th = B.map (Tw.π n) th')
    (hw : (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w))
    (hw' : (p ^ (n + 1)) • th' = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w')) :
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w = LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w' := by
  have hd : B.map (Tw.π n) (th - th') = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨v0, hv0⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 hd
  have hp : (p ^ (n + 1)) • th = (p ^ (n + 1)) • th' := by
    have h : (p ^ (n + 1)) • (th - th') = 0 := by
      rw [← hv0, ← map_nsmul, B.nsmul_ker_zero Tw n v0, map_zero]
    rwa [smul_sub, sub_eq_zero] at h
  rw [hw, hw'] at hp
  have hx := B.tg_inj (Tw.π n) (Tw.sqZero n) hp
  obtain ⟨g', hg'⟩ := Tw.exists_factor n
  rw [← hg', LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (LinearMap.lTensor B.gg g') hx

end BX

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.ProdPowUnitVectorVal
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def e1 (l : Ix g) : Nb p g := Pi.single l 1

def hvec (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) : R := uR hv D j y ^ p

def bR (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) : Nb p g → R :=
  (MuR hv D)⁻¹ *ᵥ hvec hv D j

def epow (D : Lifts H U X) (α : Nb p g) : R := ∏ j, D.ε j ^ (α j).val

theorem unitVector_val (l j : Ix g) : ((e1 (p := p) l) j).val = if j = l then 1 else 0 := by
  unfold e1
  by_cases h : j = l
  · subst h
    simp [ZMod.val_one]
  · simp [Pi.single_apply, h]

theorem prod_pow_unitVector_val {M : Type} [CommMonoid M] (f : Ix g → M) (l : Ix g) :
    ∏ j, f j ^ ((e1 (p := p) l) j).val = f l := by
  simp only [unitVector_val]
  rw [Finset.prod_eq_single l (fun j _ hj => by rw [if_neg hj, pow_zero]) (by simp), if_pos rfl,
    pow_one]

theorem liftScalePow_unitVector (D : Lifts H U X) (l : Ix g) : epow D (e1 (p := p) l) = D.ε l := by
  exact prod_pow_unitVector_val D.ε l

theorem MuR_mulVec_bR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j : Ix g) : MuR hv D *ᵥ bR hv D j = hvec hv D j := by
  rw [bR, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_MuR hv hp1 D),
    Matrix.one_mulVec]

theorem mulVec_inj (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    {a b : Nb p g → R} (h : MuR hv D *ᵥ a = MuR hv D *ᵥ b) : a = b := by
  have h1 := congrArg (fun w => (MuR hv D)⁻¹ *ᵥ w) h
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_MuR hv hp1 D),
    Matrix.one_mulVec] using h1

theorem linX_xp (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) :
    linX D (fun y => xL D j y ^ p) l =
      algebraMap R C (bR hv D j (e1 l)) * (algebraMap R C (D.ε j) ^ p / algebraMap R C (D.ε l)) := by
  have hdet := det_valM_ne hv hp1 D
  have hE : ∀ α, algebraMap R C (epow D α) ≠ 0 := by
    intro α
    simp only [epow, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      pow_ne_zero _ (fun h0 => D.ε_ne j (hv.hom_inj (h0.trans (map_zero _).symm)))
  have hf : (fun y => xL D j y ^ p) = valM D *ᵥ (fun α => algebraMap R C (D.ε j) ^ p *
      algebraMap R C (bR hv D j α) / algebraMap R C (epow D α)) := by
    funext y
    simp only [Matrix.mulVec, dotProduct, valM_eq hv D, Matrix.mul_diagonal, Matrix.map_apply]
    have h2 := congrFun (MuR_mulVec_bR hv hp1 D j) y
    simp only [Matrix.mulVec, dotProduct, hvec] at h2
    have h3 := congrArg (algebraMap R C) h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_pow, uR_spec] at h3
    simp only [map_mul] at h3
    rw [xL, mul_pow, ← h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h4 := hE α
    simp only [epow] at h4 ⊢
    field_simp
  unfold linX coefX
  rw [hf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]
  show algebraMap R C (D.ε j) ^ p * algebraMap R C (bR hv D j (e1 l)) /
    algebraMap R C (epow D (e1 l)) = _
  rw [liftScalePow_unitVector]
  ring

def psi (a : O) (y : Nb p g) : Nb p g := ((H.ρ a).map PadicInt.toZMod) *ᵥ y

theorem red_mulVec (M : Matrix (Ix g) (Ix g) ℤ_[p]) (t : TT p g) :
    red p g (M *ᵥ t) = (M.map PadicInt.toZMod) *ᵥ red p g t := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [red, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem red_surj (y : Nb p g) : ∃ t : TT p g, red p g t = y := by
  exact ⟨fun i => ((y i).val : ℤ_[p]), funext fun i => by simp [red]⟩

theorem u_psi (D : Lifts H U X) (j : Ix g) (k : Fin D.s) (y : Nb p g) :
    D.u j (psi (H := H) (D.b k) y) = algebraMap R C (U.sg (D.κ j) (D.b k)) * D.u j y := by
  obtain ⟨t, rfl⟩ := red_surj y
  have h := D.eig j k t
  rw [red_mulVec] at h
  exact h

theorem uR_psi (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (k : Fin D.s) (y : Nb p g) :
    uR hv D j (psi (H := H) (D.b k) y) = U.sg (D.κ j) (D.b k) * uR hv D j y := by
  apply hv.hom_inj
  rw [uR_spec, map_mul, uR_spec, u_psi]

theorem bR_eig (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j : Ix g) (k : Fin D.s) (α : Nb p g) :
    (∏ j', U.sg (D.κ j') (D.b k) ^ (α j').val) * bR hv D j α =
      U.sg (U.φ (D.κ j)) (D.b k) * bR hv D j α := by
  have key : MuR hv D *ᵥ (fun α => (∏ j', U.sg (D.κ j') (D.b k) ^ (α j').val) * bR hv D j α) =
      MuR hv D *ᵥ (fun α => U.sg (U.φ (D.κ j)) (D.b k) * bR hv D j α) := by
    funext y
    have h1 := congrFun (MuR_mulVec_bR hv hp1 D j) (psi (H := H) (D.b k) y)
    have h2 := congrFun (MuR_mulVec_bR hv hp1 D j) y
    simp only [Matrix.mulVec, dotProduct, MuR, Matrix.of_apply, hvec] at h1 h2 ⊢
    simp only [uR_psi, mul_pow, Finset.prod_mul_distrib] at h1
    calc ∑ α, (∏ j', uR hv D j' y ^ (α j').val) *
          ((∏ j', U.sg (D.κ j') (D.b k) ^ (α j').val) * bR hv D j α)
        = ∑ α, (∏ j', U.sg (D.κ j') (D.b k) ^ (α j').val) * (∏ j', uR hv D j' y ^ (α j').val) *
            bR hv D j α := Finset.sum_congr rfl fun α _ => by ring
      _ = U.sg (D.κ j) (D.b k) ^ p * uR hv D j y ^ p := h1
      _ = U.sg (D.κ j) (D.b k) ^ p * ∑ α, (∏ j', uR hv D j' y ^ (α j').val) * bR hv D j α := by
          rw [h2]
      _ = ∑ α, (∏ j', uR hv D j' y ^ (α j').val) * (U.sg (U.φ (D.κ j)) (D.b k) * bR hv D j α) := by
          rw [D.frobChar, Finset.mul_sum]
          exact Finset.sum_congr rfl fun α _ => by ring
  exact congrFun (mulVec_inj hv hp1 D key) α

theorem bR_off (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) (hl : D.κ l ≠ U.φ (D.κ j)) : bR hv D j (e1 l) = 0 := by
  obtain ⟨j'', hj''⟩ : ∃ j'', D.κ j'' = U.φ (D.κ j) := by
    have h := D.card_phi (D.κ j)
    have hpos : 0 < (Finset.univ.filter fun j' => D.κ j' = D.κ j).card :=
      Finset.card_pos.mpr ⟨j, by simp⟩
    rw [← h] at hpos
    obtain ⟨j'', hj''⟩ := Finset.card_pos.mp hpos
    exact ⟨j'', (Finset.mem_filter.mp hj'').2⟩
  obtain ⟨k, hk⟩ := D.sep l j'' (by rw [hj'']; exact hl)
  have he := bR_eig hv hp1 D j k (e1 l)
  rw [prod_pow_unitVector_val, ← hj''] at he
  have h0 : (U.sg (D.κ l) (D.b k) - U.sg (D.κ j'') (D.b k)) * bR hv D j (e1 l) = 0 := by
    rw [sub_mul, he, sub_self]
  have hne : U.sg (D.κ l) (D.b k) - U.sg (D.κ j'') (D.b k) ≠ 0 := by
    intro h0'
    rw [h0', map_zero, map_zero] at hk
    exact zero_ne_one hk
  have h2 := congrArg (algebraMap R C) h0
  rw [map_mul, map_zero] at h2
  have h3 : algebraMap R C (bR hv D j (e1 l)) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (hv.hom_inj (h.trans (map_zero _).symm)) hne
    · exact h
  exact hv.hom_inj (h3.trans (map_zero _).symm)

end ReciprocityTheory.PGsh.Up.UnitVectorPowers
end
end

