module

public import Development.EtaleCohomology.DivisorCycles.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.DivisorCycles.ProjPf
section
open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ProjPf

variable {C : Type} [Field C] {N n : ℕ}

theorem root_minpoly (X : LateralTheory.DivDb.Mat C N) (c : C) (h : X.charpoly.IsRoot c) :
    (minpoly C X).IsRoot c := by
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' X) c :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [Matrix.charpoly_toLin']; exact h)
  rw [← Matrix.minpoly_toLin']
  exact Module.End.hasEigenvalue_iff_isRoot.1 h1

theorem prod_dvd (e : Fin n → C) (he : Function.Injective e) (f : C[X]) (hf : ∀ k, f.eval (e k) = 0) :
    (∏ k, (X - Polynomial.C (e k))) ∣ f := by
  apply Finset.prod_dvd_of_coprime
  · exact fun a _ b _ hab => Polynomial.pairwise_coprime_X_sub_C he hab
  · intro k _; exact Polynomial.dvd_iff_isRoot.2 (hf k)

theorem minpoly_eq (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) :
    minpoly C X = ∏ k, (Polynomial.X - Polynomial.C (e k)) := by
  obtain ⟨q, hq0, hqd, hq⟩ := hD
  have hint : IsIntegral C X := Matrix.isIntegral X
  have hmon : (minpoly C X).Monic := minpoly.monic hint
  have hdvd : (∏ k, (Polynomial.X - Polynomial.C (e k))) ∣ minpoly C X :=
    prod_dvd e he _ (fun k => root_minpoly X _ (hr k))
  have hPm : (∏ k, (Polynomial.X - Polynomial.C (e k))).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
  have hdeg : (minpoly C X).natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd C X hq) hq0
    omega
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPm hmon hdvd
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact hdeg

theorem evb (e : Fin n → C) (he : Function.Injective e) (i k : Fin n) :
    (Lagrange.basis Finset.univ e i).eval (e k) = if k = i then 1 else 0 := by
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self he.injOn (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)

theorem vanish (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) (f : C[X])
    (hf : ∀ k, f.eval (e k) = 0) : aeval X f = 0 := by
  rw [← minpoly.dvd_iff, minpoly_eq X e he hD hr]
  exact prod_dvd e he f hf

end LateralTheory.DivDb.ProjPf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.ProjPf

theorem Proj_of : Proj := by
  intro C _ N n X e he hD hr
  classical
  set b : Fin n → C[X] := fun i => Lagrange.basis Finset.univ e i with hb
  have V := vanish X e he hD hr
  refine ⟨fun i => aeval X (b i), ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩, ?_, fun i => ?_⟩
  · show aeval X (b i) * aeval X (b i) = aeval X (b i)
    rw [← sub_eq_zero, ← map_mul, ← map_sub]
    apply V; intro k
    simp only [hb, eval_sub, eval_mul, evb e he]
    split_ifs <;> simp
  · show aeval X (b i) * aeval X (b j) = 0
    rw [← map_mul]
    apply V; intro k
    simp only [hb, eval_mul, evb e he]
    split_ifs with h1 h2 <;> simp_all
  · show ∑ i, aeval X (b i) = 1
    have h : aeval X (∑ i, b i - 1) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_finsetSum, evb e he, eval_one]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_one, map_sum, sub_eq_zero] at h
    exact h
  · intro h0
    have h1 : minpoly C X ∣ b i := (minpoly.dvd_iff).2 h0
    rw [minpoly_eq X e he hD hr] at h1
    have hne : b i ≠ 0 := Lagrange.basis_ne_zero he.injOn (Finset.mem_univ _)
    have h2 := Polynomial.natDegree_le_of_dvd h1 hne
    rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)] at h2
    have h3 : (b i).natDegree = n - 1 := by
      simp only [hb]
      rw [Lagrange.natDegree_basis he.injOn (Finset.mem_univ _)]
      simp
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at h2
    have := i.pos
    omega
  · have : aeval X (Polynomial.X - ∑ i, Polynomial.C (e i) * b i) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_X, eval_finsetSum, eval_mul, eval_C, evb e he]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, aeval_X, map_sum, sub_eq_zero] at this
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, aeval_C, Algebra.smul_def]
  · exact Polynomial.aeval_mem_adjoin_singleton C _

end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.SemisPf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.SemisPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

def img {A : Subalgebra C (Mat C N)} (I : Ideal A) : Submodule C (Fin N → C) :=
  Submodule.span C {w | ∃ x ∈ I, ∃ v, w = (x : Mat C N) *ᵥ v}

lemma img_step {A : Subalgebra C (Mat C N)} (J I : Ideal A) {x : A} (hx : x ∈ J) {u : Fin N → C}
    (hu : u ∈ img I) : (x : Mat C N) *ᵥ u ∈ img (J * I) := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨x * y, Submodule.mul_mem_mul hx hy, v, ?_⟩
    simp [Matrix.mulVec_mulVec]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha

lemma img_bot {A : Subalgebra C (Mat C N)} : img (⊥ : Ideal A) = ⊥ := by
  rw [img, Submodule.span_eq_bot]
  rintro w ⟨x, hx, v, rfl⟩
  rw [Submodule.mem_bot] at hx
  simp [hx]

lemma conj_pow (P B Q : Mat C N) (h : Q * P = 1) (n : ℕ) : (P * B * Q) ^ (n + 1) = P * B ^ (n + 1) * Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ B (n+1)]
    calc P * B ^ (n + 1) * Q * (P * B * Q) = P * B ^ (n + 1) * (Q * P) * B * Q := by noncomm_ring
      _ = _ := by rw [h]; noncomm_ring

lemma nil_conj (P B Q : Mat C N) (h : Q * P = 1) (hB : IsNilpotent B) : IsNilpotent (P * B * Q) := by
  obtain ⟨k, hk⟩ := hB
  refine ⟨k + 1, ?_⟩
  rw [conj_pow P B Q h, pow_succ, hk]; simp

lemma inv_mul_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

lemma mul_inv_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem Semis_of : Semis := by
  intro Γ C _ _ N ρ A hss hn hk Y hYA hY

  let S : Set (Mat C N) := {Z | Z ∈ A ∧ ∀ a ∈ A, IsNilpotent (a * Z)}
  let U : Submodule C (Fin N → C) := Submodule.span C {w | ∃ Z ∈ S, ∃ v, w = Z *ᵥ v}
  have hUst : ∀ g, ∀ v ∈ U, (ρ g : Mat C N) *ᵥ v ∈ U := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨Z, ⟨hZA, hZ⟩, v, rfl⟩ := hw
      refine Submodule.subset_span ⟨(ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N), ⟨hn g Z hZA, ?_⟩,
        (ρ g : Mat C N) *ᵥ v, ?_⟩
      · intro a ha
        have ha' : (ρ g⁻¹ : Mat C N) * a * (ρ g⁻¹⁻¹ : Mat C N) ∈ A := hn g⁻¹ a ha
        rw [inv_inv] at ha'
        have := nil_conj (ρ g : Mat C N) ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N) * Z)
          (ρ g⁻¹ : Mat C N) (inv_mul_rho ρ g) (hZ ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N)) ha')
        convert this using 1
        calc a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N))
            = ((ρ g : Mat C N) * (ρ g⁻¹ : Mat C N)) * a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N)) := by
              rw [mul_inv_rho]; simp
          _ = _ := by noncomm_ring
      · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc ((ρ g : Mat C N) * Z), inv_mul_rho, mul_one]
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
    | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨W, hcompl, hWst⟩ := hss U hUst
  have hWA := hk W hWst
  have hkill : ∀ Z ∈ S, ∀ w ∈ W, Z *ᵥ w = 0 := by
    intro Z hZ w hw
    have h1 : Z *ᵥ w ∈ U := Submodule.subset_span ⟨Z, hZ, w, rfl⟩
    have h2 : Z *ᵥ w ∈ W := hWA Z hZ.1 w hw
    have := hcompl.inf_eq_bot
    have h3 : Z *ᵥ w ∈ U ⊓ W := ⟨h1, h2⟩
    rw [this] at h3
    exact (Submodule.mem_bot C).1 h3
  have : IsArtinianRing A := IsArtinianRing.of_finite C A
  let J : Ideal A := Ideal.jacobson ⊥
  have hSJ : ∀ Z (hZ : Z ∈ S), (⟨Z, hZ.1⟩ : A) ∈ J := by
    intro Z hZ
    rw [Ideal.mem_jacobson_iff]
    intro y
    have hnil : IsNilpotent (y * (⟨Z, hZ.1⟩ : A)) := by
      obtain ⟨k, hk'⟩ := hZ.2 y y.2
      refine ⟨k, Subtype.ext ?_⟩
      simpa using hk'
    have hu := hnil.isUnit_one_add
    refine ⟨↑hu.unit⁻¹, ?_⟩
    rw [Ideal.mem_bot]
    have h1 : (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) = 1 := hu.val_inv_mul
    calc (↑hu.unit⁻¹ : A) * y * (⟨Z, hZ.1⟩ : A) + ↑hu.unit⁻¹ - 1
        = (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) - 1 := by noncomm_ring
      _ = 0 := by rw [h1, sub_self]
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have key : ∀ k : ℕ, U ≤ img (J ^ (k + 1)) := by
    intro k
    induction k with
    | zero =>
      rw [Submodule.pow_one]
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      exact Submodule.subset_span ⟨⟨Z, hZ.1⟩, hSJ Z hZ, v, rfl⟩
    | succ k ih =>
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      have hv : v ∈ U ⊔ W := hcompl.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
      show Z *ᵥ (u + w') ∈ img (J ^ (k + 1 + 1))
      rw [Matrix.mulVec_add, hkill Z hZ w' hw', add_zero, Ideal.IsTwoSided.pow_succ]
      exact img_step J _ (x := ⟨Z, hZ.1⟩) (hSJ Z hZ) (ih hu)
  have hU : U = ⊥ := by
    have h := key m
    have hb : J ^ (m + 1) = ⊥ := by
      rw [Submodule.pow_succ, hm, Submodule.zero_eq_bot, Submodule.bot_mul]
    rw [hb, img_bot] at h
    exact le_bot_iff.1 h
  ext i j
  have hv : Y *ᵥ Pi.single j 1 ∈ U := Submodule.subset_span ⟨Y, ⟨hYA, hY⟩, Pi.single j 1, rfl⟩
  rw [hU, Submodule.mem_bot] at hv
  simpa using congrFun hv i
end LateralTheory.DivDb.SemisPf
end

-- bundled from Development.EtaleCohomology.DivisorCycles.SumMulSum
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.KeyPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

theorem sum_mul_p {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (k : Fin n) :
    (∑ j, d j • p j) * p k = d k • p k := by
  rw [Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, (hS.1.idem k).eq]
  · intro j _ hj; rw [smul_mul_assoc, hS.1.ortho hj, smul_zero]
  · simp

theorem p_mul_sum {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (k : Fin n) :
    p k * (∑ j, d j • p j) = d k • p k := by
  rw [Finset.mul_sum, Finset.sum_eq_single k]
  · rw [mul_smul_comm, (hS.1.idem k).eq]
  · intro j _ hj; rw [mul_smul_comm, hS.1.ortho (Ne.symm hj), smul_zero]
  · simp

theorem sum_mul_sum {p : Fin n → Mat C N} (hS : Sys p) (d d' : Fin n → C) :
    (∑ j, d j • p j) * (∑ j, d' j • p j) = ∑ j, (d j * d' j) • p j := by
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, p_mul_sum hS, smul_smul]

theorem sum_inv {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (hd : ∀ j, d j ≠ 0) :
    (∑ j, d j • p j) * (∑ j, (d j)⁻¹ • p j) = 1 ∧ (∑ j, (d j)⁻¹ • p j) * (∑ j, d j • p j) = 1 := by
  rw [sum_mul_sum hS, sum_mul_sum hS]
  simp only [mul_inv_cancel₀ (hd _), inv_mul_cancel₀ (hd _), one_smul, hS.1.complete, and_self]

theorem sum_mem {p : Fin n → Mat C N} (A : Subalgebra C (Mat C N)) (hp : ∀ i, p i ∈ A) (d : Fin n → C) :
    (∑ j, d j • p j) ∈ A :=
  Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (hp j) _

theorem inv_in (A : Subalgebra C (Mat C N)) {v : Mat C N} (hvA : v ∈ A) (hv : IsUnit v) :
    ∃ w ∈ A, v * w = 1 := by
  let a : A := ⟨v, hvA⟩
  have hinj : Function.Injective A.val := Subtype.val_injective
  have ha : a ∈ nonZeroDivisors A := comap_nonZeroDivisors_le_of_injective hinj hv.mem_nonZeroDivisors
  haveI : Module.Finite C A := FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule A)
  have hu : IsUnit a := IsArtinianRing.isUnit_of_nonZeroDivisor_of_isIntegral' (R := C) ha
  obtain ⟨b, hb⟩ := hu
  refine ⟨((b⁻¹ : Aˣ) : A), ((b⁻¹ : Aˣ) : A).2, ?_⟩
  have := congrArg Subtype.val b.mul_inv
  rw [hb] at this; exact this

theorem zcl_sub (S : Set (Mat C N)) : S ⊆ Zcl S := fun x hx _ hf => hf x hx

theorem zcl_mono {S T : Set (Mat C N)} (h : S ⊆ T) : Zcl S ⊆ Zcl T :=
  fun y hy f hf => hy f fun x hx => hf x (h hx)

end LateralTheory.DivDb.KeyPf

namespace LateralTheory.DivDb.KeyPf
open LateralTheory.DivDb
variable {C : Type} [Field C] {N n : ℕ}

theorem sys_conj {p : Fin n → Mat C N} (hS : Sys p) (R Ri : Mat C N) (h1 : ∀ X, R * (Ri * X) = X)
    (h2 : ∀ X, Ri * (R * X) = X) : Sys (fun j => Ri * p j * R) := by
  have h2' : ∀ X, Ri * (R * X) = X := h2
  refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i h => hS.2 i ?_⟩
  · show Ri * p i * R * (Ri * p i * R) = Ri * p i * R
    simp only [mul_assoc, h1]; rw [← mul_assoc (p i), (hS.1.idem i).eq]
  · show Ri * p i * R * (Ri * p j * R) = 0
    simp only [mul_assoc, h1]; rw [← mul_assoc (p i), hS.1.ortho hij]; simp
  · rw [← Finset.sum_mul, ← Finset.mul_sum, hS.1.complete, mul_one]
    have := h2 1; simpa using this
  · have := congrArg (fun Y => R * Y * Ri) h
    simp only [mul_assoc, h1, mul_zero, zero_mul] at this
    have e' : R * Ri = 1 := by simpa using h1 1
    rwa [e', mul_one] at this

theorem tv_zcl {ρS : Submonoid (Mat C N)} (hZM : ZclMul) (hUn : Unip) [CharZero C]
    (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (hS : Sys p)
    (hT : ∀ a ∈ A, ∀ j k, j ≠ k → p j * a * p k ∈ Tan (ρS : Set (Mat C N))) :
    ∀ u ∈ Tv A p, u ∈ Zcl (ρS : Set (Mat C N)) := by
  intro u hu
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, j, k, hjk, rfl⟩ := hx
    apply hUn C N ρS _ (hT a ha j k hjk)
    have : p k * p j = 0 := hS.1.ortho (Ne.symm hjk)
    calc p j * a * p k * (p j * a * p k) = p j * a * (p k * p j) * a * p k := by simp only [mul_assoc]
      _ = 0 := by rw [this]; simp
  | one => exact zcl_sub _ ρS.one_mem
  | mul x y _ _ hx hy => exact hZM C N ρS x hx y hy

theorem Key_of (hIC : IdemConj) (hMU : MatrixUnits₂) (hUF : UnitFactorization) (hTI : TanIndex) (hUn : Unip)
    (hZM : ZclMul) (hGS : GenSpec) (hTP : TorusPt) (hTD : TanDeg) (hCC : CycleCount) : Key := by
  intro Γ C _ _ _ _ N n ρ e p hDeg hLac hG U hU hUf g
  obtain ⟨hS, hX, hCo, hNN, hNo, _hKe, hOff⟩ := hG
  have hRiR : (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hRRi : (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  set R : Mat C N := (ρ g : Mat C N) with hRdef
  set Ri : Mat C N := (ρ g⁻¹ : Mat C N) with hRidef
  have h1 : ∀ X, R * (Ri * X) = X := fun X => by rw [← mul_assoc, hRRi, one_mul]
  have h2 : ∀ X, Ri * (R * X) = X := fun X => by rw [← mul_assoc, hRiR, one_mul]
  set A := env ρ
  have hSq := sys_conj hS R Ri h1 h2
  have hCq : Corner A (fun j => Ri * p j * R) := by
    refine ⟨fun i => ?_, fun a ha i => ?_⟩
    · have := hNo g⁻¹ (p i) (hCo.1 i); rwa [inv_inv] at this
    · obtain ⟨c, hc⟩ := hCo.2 _ (hNo g a ha) i
      refine ⟨c, ?_⟩
      calc Ri * p i * R * a * (Ri * p i * R) = Ri * (p i * (R * a * Ri) * p i) * R := by
            simp only [mul_assoc]
        _ = c • (Ri * p i * R) := by rw [hc]; simp only [mul_smul_comm, smul_mul_assoc]
  obtain ⟨v, hvA, hvU, π, hvπ, hπ⟩ := hIC C N n A p _ hS hCo hSq hCq hNN
  obtain ⟨E, hE⟩ := hMU C N n A p hS hCo hNN
  obtain ⟨u, huT, d, hd, hvud⟩ := hUF C N n A p E hS hE v hvA hvU
  obtain ⟨hDD', hD'D⟩ := sum_inv hS d hd
  have hu : u = v * ∑ j, (d j)⁻¹ • p j := by rw [hvud, mul_assoc, hDD', mul_one]
  have hup : ∀ j, u * p j = Ri * p (π j) * R * u := by
    intro j
    have e1 : u * p j = v * ((d j)⁻¹ • p j) := by rw [hu, mul_assoc, sum_mul_p hS]
    have e2 : Ri * p (π j) * R * u = v * ((d j)⁻¹ • p j) := by
      rw [hu, ← mul_assoc, ← hvπ j, mul_assoc, p_mul_sum hS]
    rw [e1, e2]
  have hxp : ∀ j, R * u * p j = p (π j) * (R * u) := by
    intro j; rw [mul_assoc, hup]; simp only [mul_assoc, h1]
  have hD'U : IsUnit (∑ j, (d j)⁻¹ • p j) := ⟨⟨_, _, hD'D, hDD'⟩, rfl⟩
  have huU : IsUnit u := by rw [hu]; exact hvU.mul hD'U
  have hxU : IsUnit (R * u) := (Units.isUnit (ρ g)).mul huU
  obtain ⟨B, hBf, hB⟩ := hGS C N n p (R * u) π hS hxU hxp
  have hXT := hTI Γ C N ρ U hU hUf hX
  obtain ⟨τ, hτ, htZ, hτB⟩ := hTP C N n (img ρ U) p e hS hLac hXT B hBf
  have hdisj := hB τ hτ hτB
  obtain ⟨hTT', hT'T⟩ := sum_inv hS τ hτ
  set t := ∑ j, τ j • p j with htdef
  have huZ : u ∈ Zcl (img ρ U : Set (Mat C N)) :=
    tv_zcl hZM hUn A p hS (fun a ha j k hjk => hTI Γ C N ρ U hU hUf (hOff a ha j k hjk)) u huT
  have hmZ := hZM C N (img ρ U) u huZ t htZ
  have htU : IsUnit t := ⟨⟨_, _, hTT', hT'T⟩, rfl⟩
  have hyU : IsUnit (R * u * t) := hxU.mul htU
  have hyp : ∀ j, R * u * t * p j = p (π j) * (R * u * t) := by
    intro j
    rw [mul_assoc, sum_mul_p hS, ← mul_assoc (p _), ← hxp, mul_assoc, mul_assoc, p_mul_sum hS]
    simp only [mul_assoc]
  have himg : ∀ y ∈ img ρ U, y ∈ img ρ ⊤ := fun y hy => by
    obtain ⟨w, -, rfl⟩ := Submonoid.mem_map.mp hy
    exact Submonoid.mem_map.mpr ⟨w, by simp, rfl⟩
  have hdegS : ∀ x ∈ img ρ ⊤, Deg n x := fun x hx => by
    obtain ⟨w, -, rfl⟩ := Submonoid.mem_map.mp hx
    exact hDeg w
  have hRZ : R ∈ Zcl (img ρ ⊤ : Set (Mat C N)) :=
    zcl_sub _ (Submonoid.mem_map.mpr ⟨g, by simp, rfl⟩)
  have hyZ : R * u * t ∈ Zcl (img ρ ⊤ : Set (Mat C N)) := by
    rw [mul_assoc]; exact hZM C N _ R hRZ _ (zcl_mono himg hmZ)
  have hyDeg := (hTD C N n (img ρ ⊤) hdegS).1 _ hyZ
  obtain ⟨hEig, hfix⟩ := hCC C N n p (R * u * t) π hS hyU hyp hyDeg hdisj
  refine ⟨⟨u * t, hmZ, by rw [← mul_assoc]; exact hEig⟩, ?_⟩
  rintro i ⟨a, haA, hne⟩
  have ha' : Ri * a * R ∈ A := by have := hNo g⁻¹ a haA; rwa [inv_inv] at this
  have hπi : π i = i := by
    refine hπ i ⟨Ri * a * R, ha', fun h => hne ?_⟩
    have := congrArg (fun Y => R * Y) h
    simp only [mul_assoc, h1, mul_zero] at this
    simpa [mul_assoc] using this
  obtain ⟨c, hc⟩ := hfix i hπi
  have hpy : p i * (R * u * t) = c • p i := by rw [← hc, hyp i, hπi]
  obtain ⟨vi, hviA, hvvi⟩ := inv_in A hvA hvU
  set D := ∑ j, d j • p j
  set T' := ∑ j, (τ j)⁻¹ • p j
  have hm1 : u * t * (T' * D * vi) = 1 := by
    have ht' : ∀ X, t * (T' * X) = X := fun X => by rw [← mul_assoc, hTT', one_mul]
    have hd' : ∀ X, (∑ j, (d j)⁻¹ • p j) * (D * X) = X := fun X => by rw [← mul_assoc, hD'D, one_mul]
    rw [hu]; simp only [mul_assoc, ht', hd', hvvi]
  refine ⟨c • (T' * D * vi), Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (sum_mem A hCo.1 _) (sum_mem A hCo.1 _)) hviA) _, ?_⟩
  calc p i * R = p i * R * (u * t * (T' * D * vi)) := by rw [hm1, mul_one]
    _ = p i * (R * u * t) * (T' * D * vi) := by simp only [mul_assoc]
    _ = p i * (c • (T' * D * vi)) := by rw [hpy, smul_mul_assoc, mul_smul_comm]

end LateralTheory.DivDb.KeyPf
end

