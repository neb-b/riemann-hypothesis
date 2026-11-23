module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualB
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatIntFMat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Vi

lemma mt_mul' (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

lemma mt_one' (V : HSp D) : mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

lemma splitIdem_eps {e' : AE D} (h : IsSplitIdem D e') : (e' + cA D e') * fI D = e' + cA D e' := by
  obtain ⟨-, -, v, ε, hε, hsum⟩ := h
  unfold Formalism.L2.Theta.IsPlaceIdem at hε
  obtain ⟨α, rfl, -, -⟩ := hε
  rw [hsum]
  unfold fI
  rw [← map_mul]
  congr 1
  all_goals first
    | rfl
    | (simp only [pairA]; exact Prod.ext (mul_zero _) (mul_one _))
    | (simp only [pairA]; ext <;> simp)

lemma supp_fin {e' : AE D} (he : IsSplitIdem D e') {V : HSp D} {g : GA D V} (hg : SuppAt e' V g) (i j : Fin V.rank) :
    (mt V g - 1) i j * fI D = (mt V g - 1) i j := by
  unfold SuppAt at hg
  conv_lhs => rw [← hg i j]
  rw [mul_right_comm, splitIdem_eps he, hg i j]

lemma supp_inv {e' : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e' V g) : SuppAt e' V g⁻¹ := by
  unfold SuppAt at hg ⊢
  intro i j
  have hinv : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1)) := by
    rw [Matrix.mul_sub, ← mt_mul', inv_mul_cancel, mt_one', Matrix.mul_one]
    abel
  rw [hinv, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k j]

lemma intF_matMul {m n p : ℕ} {A : Matrix (Fin m) (Fin n) (AE D)} {B : Matrix (Fin n) (Fin p) (AE D)}
    (hA : ∀ i j, IntF (A i j)) (hB : ∀ i j, IntF (B i j)) (i : Fin m) (j : Fin p) : IntF ((A * B) i j) := by
  rw [Matrix.mul_apply]
  exact intF_sum _ _ fun k _ => intF_mul (hA i k) (hB k j)

lemma exists_nat_intF_mat {m n : ℕ} {A : Matrix (Fin m) (Fin n) (AE D)} (hA : ∀ i j, A i j * fI D = A i j) :
    ∃ k : ℕ, 0 < k ∧ ∀ i j, IntF ((k • A) i j) := by
  choose k hk0 hk using fun (i : Fin m) (j : Fin n) => exists_nat_intF (hA i j)
  refine ⟨∏ i, ∏ j, k i j, Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => hk0 i j, fun i j => ?_⟩
  obtain ⟨r, hr⟩ : k i j ∣ ∏ i, ∏ j, k i j :=
    (Finset.dvd_prod_of_mem (fun j => k i j) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, k i j) (Finset.mem_univ i))
  rw [Matrix.smul_apply, hr, mul_comm (k i j) r, mul_smul]
  exact intF_nsmul (hk i j) r

lemma actO_expand {S T : HSp D} (g : GA D S) (h : GA D T) (t : WO S T) :
    actO S T g h t = t + (mt T h - 1) * t + t * (mt S g⁻¹ - 1) + (mt T h - 1) * t * (mt S g⁻¹ - 1) := by
  unfold actO
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  abel

lemma nsmul_mul_nsmul {R : Type*} [CommRing R] {m n p : Type*} [Fintype n] (a b : ℕ) (A : Matrix m n R)
    (B : Matrix n p R) : (a • A) * (b • B) = (a * b) • (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

lemma nsmul_mul_three {R : Type*} [CommRing R] {m n p q : Type*} [Fintype n] [Fintype p] (a b d : ℕ) (A : Matrix m n R)
    (B : Matrix n p R) (C : Matrix p q R) : (a • A) * (b • B) * (d • C) = (a * b * d) • (A * B * C) := by
  rw [nsmul_mul_nsmul, nsmul_mul_nsmul]

set_option maxHeartbeats 800000 in
lemma four_terms {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {c c' kH kG : ℕ}
    (hlow : ∀ Z : WO S T, (∀ i j, IntF (Z i j)) → c • Z ∈ latAll S T ΛS ΛT)
    {H : Matrix (Fin T.rank) (Fin T.rank) (AE D)} {G' : Matrix (Fin S.rank) (Fin S.rank) (AE D)}
    (hH : ∀ i j, IntF ((kH • H) i j)) (hG : ∀ i j, IntF ((kG • G') i j)) {t : WO S T}
    (ht : t ∈ latAll S T ΛS ΛT) (hc't : ∀ i j, IntF ((c' • t) i j)) :
    (c * c' * kH * kG) • (t + H * t + t * G' + H * t * G') ∈ latAll S T ΛS ΛT := by
  have hZ1 : ∀ i j, IntF (((kH • H) * (c' • t)) i j) := intF_matMul hH hc't
  have hZ2 : ∀ i j, IntF (((c' • t) * (kG • G')) i j) := intF_matMul hc't hG
  have hZ3 : ∀ i j, IntF (((kH • H) * (c' • t) * (kG • G')) i j) := intF_matMul hZ1 hG
  rw [nsmul_mul_nsmul] at hZ1 hZ2
  rw [nsmul_mul_three] at hZ3
  have m1 := hlow _ hZ1
  have m2 := hlow _ hZ2
  have m3 := hlow _ hZ3
  rw [smul_smul] at m1 m2 m3
  simp only [smul_add]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
  · exact nsmul_mem ht _
  · have h1 := nsmul_mem m1 kG
    rw [smul_smul] at h1
    have e : c * c' * kH * kG = kG * (c * (kH * c')) := by ring
    rw [e]
    exact h1
  · have h2 := nsmul_mem m2 kH
    rw [smul_smul] at h2
    have e : c * c' * kH * kG = kH * (c * (c' * kG)) := by ring
    rw [e]
    exact h2
  · have e : c * c' * kH * kG = c * (kH * c' * kG) := by ring
    rw [e]
    exact m3

theorem placeLatDualVi (D : D7) : PlaceLatDualVi D := by
  intro ψ _ S T ΛS ΛT hS hT e' he' g h hg hh
  obtain ⟨c, hc, hlow⟩ := lower hS hT
  obtain ⟨c', hc', hup⟩ := upper hS hT
  obtain ⟨kH, hkH, hH⟩ := exists_nat_intF_mat (supp_fin he' hh)
  obtain ⟨kG, hkG, hG⟩ := exists_nat_intF_mat (supp_fin he' (supp_inv hg))
  refine ⟨c * c' * kH * kG, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hc hc') hkH) hkG, fun t ht => ?_⟩
  rw [actO_expand]
  exact four_terms hlow hH hG ht (hup t ht)

end Vi

end Formalism.IndefR.Fin.PDB

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatOAnnIffOf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


set_option maxHeartbeats 1600000 in
theorem exists_sub_pairA_ratW_mem_latO (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hbox : ∃ N : ℕ, 0 < N ∧ ∀ Y : WO S T, (∀ i j, finPart D (Y i j) ∈ intAE D) → (∀ i j, infPart D (Y i j) = 0) →
      N • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    (x : WO S T) (hx : x.map (infPart D) = 0) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, x - pairA D.host.F 0 1 • ratW T S γ ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨N, hN, hbox⟩ := hbox
  have hdec : ∀ i j, ∃ w : D.host.E, ∃ y ∈ intAE D, finPart D (x i j) = (1 : Af D.host.F) ⊗ₜ[D.host.F] w + N • y :=
    fun i j => approx_AfE N hN (finPart D (x i j))
  choose w y hy hwy using hdec
  refine ⟨Matrix.of w, ?_⟩
  have hY : x - pairA D.host.F 0 1 • ratW T S (Matrix.of w) = N • (Matrix.of fun i j => jF D (y i j) : WO S T) := by
    ext i j
    have hxij : infPart D (x i j) = 0 := by
      have := congrFun (congrFun hx i) j
      simpa using this
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.of_apply, eq_jF_of_inf (x i j) hxij, hwy,
      map_add, map_nsmul]
    have h1 : jF D ((1 : Af D.host.F) ⊗ₜ[D.host.F] w i j) = pairA D.host.F 0 1 • ratW T S (Matrix.of w) i j := by
      rw [jF_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      show _ = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] w i j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1, add_sub_cancel_left]
  rw [hY]
  apply hbox
  · intro i j; rw [Matrix.of_apply, finPart_jF]; exact hy i j
  · intro i j; rw [Matrix.of_apply, infPart_jF]


set_option maxHeartbeats 1600000 in
theorem ann_rat_mem (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hglob : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) →
      γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t})
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hann : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ψ (symplO S T (pairA D.host.F 0 1 • ratW T S γ) u) = 1) :
    pairA D.host.F 0 1 • ratW T S γ ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have hb : ∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F := by
    intro c hc s hs t ht y
    have hmem := gen_mem S T ΛS ΛT (intAf_int y) hc hs ht
    rw [gen_eq] at hmem
    have h := hann _ hmem
    rw [symplO_smul_left, symplO_smul_right, symplO_ratW_ratW] at h
    have e : pairA D.host.F 0 1 * (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (y : D.host.F)) *
        algebraMap D.host.F (AF D.host.F) (betaO S T γ (rk1 S T c s t))) =
        pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t) * (y : D.host.F))) := by
      refine Prod.ext (by show (0 : Ainf D.host.F) * (0 * _) = 0; rw [zero_mul]) ?_
      change 1 * (algebraMap D.host.F (Af D.host.F) (y : D.host.F) *
        algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t))) =
        algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t) * (y : D.host.F))
      rw [map_mul]; ring
    rw [e, psi_fin_rat hψ] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    refine ⟨n, ?_⟩
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((Algebra.trace ℚ D.host.F (betaO S T γ (rk1 S T c s t) * (y : D.host.F)) : ℚ) : ℂ) = (n : ℂ) := by
      have := hn
      rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)] at this
      exact mul_right_cancel₀ h2pi this
    exact_mod_cast this
  have hsp := hglob γ hb
  clear hb hann
  induction hsp using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨c, hc, s, hs, t, ht, rfl⟩ := hM
    have := gen_mem S T ΛS ΛT one_intAf hc hs ht
    rwa [gen_eq] at this
  | zero =>
    rw [show ratW T S (0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E) = 0 by ext i j; simp [ratW], smul_zero]
    exact zero_mem _
  | add M M' _ _ h1 h2 =>
    rw [show ratW T S (M + M') = ratW T S M + ratW T S M' by ext i j; simp [ratW], smul_add]
    exact add_mem h1 h2
  | smul n M _ h =>
    rw [show ratW T S (n • M) = n • ratW T S M by ext i j; simp [ratW, zsmul_eq_mul], smul_comm]
    exact zsmul_mem h n

theorem latO_ann_iff_of (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hbox : ∃ N : ℕ, 0 < N ∧ ∀ Y : WO S T, (∀ i j, finPart D (Y i j) ∈ intAE D) → (∀ i j, infPart D (Y i j) = 0) →
      N • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    (hglob : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) →
      γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t})
    (x : WO S T) (hx : x.map (infPart D) = 0) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T x u) = 1 := by
  constructor
  · intro hxm u hu; exact lat_ann hψ S T hS hT hxm hu
  · intro hann
    obtain ⟨γ, hγ⟩ := exists_sub_pairA_ratW_mem_latO S T hbox x hx
    have hann' : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T (pairA D.host.F 0 1 • ratW T S γ) u) = 1 := by
      intro u hu
      have h1 := hann u hu
      have h2 := lat_ann hψ S T hS hT hγ hu
      have e : pairA D.host.F 0 1 • ratW T S γ = x - (x - pairA D.host.F 0 1 • ratW T S γ) := by abel
      rw [e, show x - (x - pairA D.host.F 0 1 • ratW T S γ) = x + -(x - pairA D.host.F 0 1 • ratW T S γ) by abel,
        symplO_add_left, symplO_neg_left, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, h1, h2, inv_one, one_mul]
    have hr := ann_rat_mem hψ S T hglob γ hann'
    have : x = (x - pairA D.host.F 0 1 • ratW T S γ) + pairA D.host.F 0 1 • ratW T S γ := by abel
    rw [this]; exact add_mem hγ hr

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualBIv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

lemma nsmul_add' {M : Type*} [AddCommGroup M] (n : ℕ) (a b : M) : n • (a + b) = n • a + n • b :=
  smul_add n a b

lemma nsmul_neg' {M : Type*} [AddCommGroup M] (n : ℕ) (a : M) : n • (-a) = -(n • a) :=
  smul_neg n a

lemma ringInt_residues {K : Type} [Field K] [NumberField K] (N : ℕ) (hN : 0 < N) :
    ∃ R : Finset (𝓞 K), ∀ x : 𝓞 K, ∃ r ∈ R, ∃ y : 𝓞 K, x = r + (N : 𝓞 K) * y := by
  classical
  set I : Ideal (𝓞 K) := Ideal.span {(N : 𝓞 K)} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI := Fintype.ofFinite (𝓞 K ⧸ I)
  refine ⟨Finset.univ.image (fun q : 𝓞 K ⧸ I => q.out), fun x => ?_⟩
  refine ⟨(Ideal.Quotient.mk I x).out, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have h : x - (Ideal.Quotient.mk I x).out ∈ I :=
    Ideal.Quotient.eq.1 (Quotient.out_eq (Ideal.Quotient.mk I x)).symm
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨y, by linear_combination (-1 : 𝓞 K) * hy⟩

lemma finite_part_finite_embedding (w : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (finiteEmbeddingTensor D w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul β y => rfl
  | add w w' h h' => rw [map_add (f := _), map_add (f := _), h, h']

lemma integral_of_finite_embedding {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) : IntF (finiteEmbeddingTensor D w) :=
  ⟨by rw [mul_fI_eq, finite_part_finite_embedding], by rw [finite_part_finite_embedding]; exact hw⟩


set_option maxHeartbeats 800000 in
lemma intAE_decomp (N : ℕ) (hN : 0 < N) {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) :
    ∃ x : 𝓞 D.host.E, ∃ w' ∈ intAE D, w = (1 : Af D.host.F) ⊗ₜ[D.host.F] (x : D.host.E) + N • w' := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    have hN0 : ((N : 𝓞 D.host.F)) ≠ 0 := by exact_mod_cast hN.ne'
    obtain ⟨b, c, hc, hαe⟩ := Formalism.L2.S.Pv.PsiTrCore.exists_decomp α (fun v => hα v) (N : 𝓞 D.host.F) hN0
    have hx : ∃ x : 𝓞 D.host.E, (x : D.host.E) = (b : D.host.F) • (o : D.host.E) := by
      refine ⟨⟨(b : D.host.F) • (o : D.host.E), ?_⟩, rfl⟩
      rw [Algebra.smul_def]
      exact IsIntegral.mul ((RingOfIntegers.isIntegral_coe b).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E))
        (RingOfIntegers.isIntegral_coe o)
    obtain ⟨x, hx⟩ := hx
    refine ⟨x, c ⊗ₜ[D.host.F] (o : D.host.E), AddSubgroup.subset_closure ⟨c, fun v => hc v, o, rfl⟩, ?_⟩
    rw [hαe, TensorProduct.add_tmul, hx, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    congr 1
    have hNc : algebraMap D.host.F (Af D.host.F) (((N : 𝓞 D.host.F) : D.host.F)) = (N : Af D.host.F) := by
      have h1 : ((N : 𝓞 D.host.F) : D.host.F) = (N : D.host.F) := by push_cast; rfl
      rw [h1, map_natCast]
    rw [hNc, ← nsmul_eq_mul]
    exact (TensorProduct.smul_tmul' N c _).symm
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨x₁, w₁', hw₁', e₁⟩ := h₁
    obtain ⟨x₂, w₂', hw₂', e₂⟩ := h₂
    refine ⟨x₁ + x₂, w₁' + w₂', add_mem hw₁' hw₂', ?_⟩
    rw [e₁, e₂]
    push_cast
    rw [TensorProduct.tmul_add, nsmul_add']
    abel
  | neg w _ h =>
    obtain ⟨x, w', hw', e⟩ := h
    refine ⟨-x, -w', neg_mem hw', ?_⟩
    rw [e]
    push_cast
    rw [TensorProduct.tmul_neg, nsmul_neg']
    abel


set_option maxHeartbeats 800000 in
lemma intAE_residues (N : ℕ) (hN : 0 < N) :
    ∃ R : Finset (Af D.host.F ⊗[D.host.F] D.host.E), ∀ w ∈ intAE D, ∃ r ∈ R, ∃ w' ∈ intAE D, w = r + N • w' := by
  classical
  obtain ⟨RE, hRE⟩ := ringInt_residues (K := D.host.E) N hN
  refine ⟨RE.image (fun r : 𝓞 D.host.E => (1 : Af D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)), fun w hw => ?_⟩
  obtain ⟨x, w', hw', e⟩ := intAE_decomp N hN hw
  obtain ⟨r, hr, y, hy⟩ := hRE x
  have h1 : (1 : Af D.host.F) ⊗ₜ[D.host.F] (y : D.host.E) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, one_mem_intAf, y, rfl⟩
  refine ⟨_, Finset.mem_image_of_mem _ hr, (1 : Af D.host.F) ⊗ₜ[D.host.F] (y : D.host.E) + w', add_mem h1 hw', ?_⟩
  rw [e, hy]
  push_cast
  have h2 : (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * (y : D.host.E)) =
      N • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (y : D.host.E)) := by
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul]
  rw [TensorProduct.tmul_add, h2, nsmul_add']
  abel


set_option maxHeartbeats 800000 in
lemma intF_residues (N : ℕ) (hN : 0 < N) :
    ∃ R : Finset (AE D), ∀ y : AE D, IntF y → ∃ r ∈ R, ∃ y' : AE D, IntF y' ∧ y = r + N • y' := by
  classical
  obtain ⟨R, hR⟩ := intAE_residues (D := D) N hN
  refine ⟨R.image (finiteEmbeddingTensor D), fun y hy => ?_⟩
  obtain ⟨r, hr, w', hw', e⟩ := hR _ hy.2
  refine ⟨finiteEmbeddingTensor D r, Finset.mem_image_of_mem _ hr, finiteEmbeddingTensor D w', integral_of_finite_embedding hw', ?_⟩
  have hy' : y = finiteEmbeddingTensor D (finPart D y) := by rw [← mul_fI_eq, hy.1]
  rw [hy', e, map_add (f := _), map_nsmul]


set_option maxHeartbeats 800000 in
lemma mat_residues (m n : ℕ) (N : ℕ) (hN : 0 < N) :
    ∃ R : Finset (Mx D m n), ∀ Z : Mx D m n, (∀ i j, IntF (Z i j)) →
      ∃ ρ ∈ R, ∃ Z' : Mx D m n, (∀ i j, IntF (Z' i j)) ∧ Z = ρ + N • Z' := by
  classical
  obtain ⟨R1, hR1⟩ := intF_residues (D := D) N hN
  refine ⟨(Fintype.piFinset fun _ : Fin m => Fintype.piFinset fun _ : Fin n => R1).image Matrix.of,
    fun Z hZ => ?_⟩
  choose r hr y hy hyeq using fun i j => hR1 (Z i j) (hZ i j)
  refine ⟨Matrix.of r, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 fun i =>
    Fintype.mem_piFinset.2 fun j => hr i j), Matrix.of y, hy, ?_⟩
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply]
  exact hyeq i j

set_option maxHeartbeats 800000 in
lemma nsmul_cancel_AE {x y : AE D} {k : ℕ} (hk : 0 < k) (h : k • x = k • y) : x = y := by
  have hk' : ((k : D.host.F)) ≠ 0 := by exact_mod_cast hk.ne'
  have hu : algebraMap D.host.F (AE D) ((k : D.host.F))⁻¹ * algebraMap D.host.F (AE D) (k : D.host.F) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hk', map_one]
  have hkc : (k : AE D) = algebraMap D.host.F (AE D) (k : D.host.F) := (map_natCast _ k).symm
  rw [nsmul_eq_mul, nsmul_eq_mul, hkc] at h
  calc x = algebraMap D.host.F (AE D) ((k : D.host.F))⁻¹ * (algebraMap D.host.F (AE D) (k : D.host.F) * x) := by
        rw [← mul_assoc, hu, one_mul]
    _ = algebraMap D.host.F (AE D) ((k : D.host.F))⁻¹ * (algebraMap D.host.F (AE D) (k : D.host.F) * y) := by
        rw [h]
    _ = y := by rw [← mul_assoc, hu, one_mul]

lemma nsmul_cancel_Mx {m n : ℕ} {X Y : Mx D m n} {k : ℕ} (hk : 0 < k) (h : k • X = k • Y) : X = Y := by
  ext i j
  apply nsmul_cancel_AE hk
  have h1 := congrFun (congrFun h i) j
  simpa using h1


set_option maxHeartbeats 800000 in
lemma exists_finset_half_decomp {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {c' : ℕ} (hc' : 0 < c') (hup : ∀ t ∈ latAll S T ΛS ΛT, ∀ i j, IntF ((c' • t) i j))
    (k : ℕ) (hk : 0 < k) (e₁ : AE D) :
    ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v := by
  classical
  obtain ⟨c, hc, hlow⟩ := lower hS hT
  obtain ⟨RL, hRL⟩ := mat_residues (D := D) T.rank S.rank (k * c * c') (Nat.mul_pos (Nat.mul_pos hk hc) hc')
  let G : WO S T → Prop := fun ρ => ∃ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u ∧
    ∃ Z : WO S T, (∀ i j, IntF (Z i j)) ∧ c' • u = ρ + (k * c * c') • Z
  let pick : WO S T → WO S T := fun ρ => if h : G ρ then h.choose else 0
  refine ⟨(RL.filter G).image pick, fun u hu hhalf => ?_⟩
  obtain ⟨ρ, hρ, Z, hZ, hEq⟩ := hRL (c' • u) (hup u hu)
  have hG : G ρ := ⟨u, hu, hhalf, Z, hZ, hEq⟩
  have hpick : pick ρ = hG.choose := dif_pos hG
  obtain ⟨hu₀, hh₀, Z₀, hZ₀, hEq₀⟩ := hG.choose_spec
  have hZZ : ∀ i j, IntF ((Z - Z₀) i j) := fun i j => by
    rw [Matrix.sub_apply, sub_eq_add_neg]; exact intF_add (hZ i j) (intF_neg (hZ₀ i j))
  have hdiff : u - hG.choose = k • (c • (Z - Z₀)) := by
    apply nsmul_cancel_Mx hc'
    rw [smul_sub, hEq, hEq₀, add_sub_add_left_eq_sub, ← smul_sub, smul_smul, smul_smul]
    congr 1
    ring
  have hlowV := hlow _ hZZ
  generalize hV : c • (Z - Z₀) = V at hdiff hlowV
  refine ⟨pick ρ, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hρ, hG⟩), V, hlowV, fun i j => ?_, ?_⟩
  · apply nsmul_cancel_AE hk
    have h1 : (k • V) i j = (u - hG.choose) i j := by rw [hdiff]
    rw [Matrix.smul_apply, Matrix.sub_apply] at h1
    rw [← mul_smul_comm, h1, mul_sub, hhalf i j, hh₀ i j]
  · rw [hpick, ← hdiff]
    abel

theorem placeLatDualIv (D : D7) : PlaceLatDualIv D := by
  intro ψ _ S T ΛS ΛT hS hT P e _ k hk e₁ _
  obtain ⟨c', hc', hup⟩ := upper hS hT
  exact exists_finset_half_decomp hS hT hc' hup k hk e₁

end Formalism.IndefR.Fin.PDB

end
end

