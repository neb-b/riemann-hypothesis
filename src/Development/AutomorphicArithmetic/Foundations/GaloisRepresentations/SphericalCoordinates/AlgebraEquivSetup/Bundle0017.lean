module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TraceMapUnipotent
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private lemma c_re_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (τ : E →+* ℂ)
    (h : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀) : (τ (A.c : E)).re < 0 := by
  rcases InfinitePlace.mk_eq_iff.mp h with h | h
  · rw [h]; exact A.c_neg
  · have h1 := A.c_neg
    rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h1
    exact h1

private lemma dg_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.dg n i : 𝓞 E) : E) ≠ 0 := by
  have := A.c_ne
  unfold Arith.dg
  split_ifs <;> simp [this]

private lemma dg_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.dg n i : 𝓞 E) : E) = ((A.dg n i : 𝓞 E) : E) := by
  have h : A.bar (A.dg n i) = A.dg n i := by
    unfold Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

private lemma hd_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.hd n i : 𝓞 E) : E) = ((A.hd n i : 𝓞 E) : E) := by
  have h : A.bar (A.hd n i) = A.hd n i := by
    unfold Arith.hd Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

private lemma hd_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.hd n i : 𝓞 E) : E) = -(A.c : E) * ((A.dg n i : 𝓞 E) : E) := by
  simp [Arith.hd]

private lemma re_form {n : ℕ} (a : ℂ) (x : Fin n → ℂ) :
    (star x ⬝ᵥ ((Matrix.diagonal fun _ => a) *ᵥ x)).re = a.re * ∑ i, Complex.normSq (x i) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (x i) * (a * x i) = a * ((Complex.normSq (x i) : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h, Complex.re_mul_ofReal]

private lemma sum_pos' {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < ∑ i, Complex.normSq (x i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

private lemma form_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (e : E →+* ℂ) :
    ((A.H n).map e)ᵀ * (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)⁻¹).map e =
      Matrix.diagonal fun _ => -e (A.c : E) := by
  unfold Arith.H
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [hd_eq, map_mul, map_neg, map_inv₀, mul_assoc, mul_inv_cancel₀ ((map_ne_zero e).2 (dg_ne A n i)), mul_one]

private lemma H_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    (A.H n).map (cj E) = A.H n := by
  unfold Arith.H
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact hd_cj A n i

private abbrev Dm {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) : Matrix (Fin n) (Fin n) E :=
  Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)

private lemma H_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    A.H n = (-(A.c : E)) • Dm A n := by
  unfold Arith.H
  ext i j
  by_cases h : i = j
  · subst h; simp [hd_eq]
  · simp [h]

private lemma D_star {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) :
    Dm A n * (hermStar (A.H n) (A.det_ne n) M).unop = (M.map (cj E))ᵀ * Dm A n := by
  have hc : -(A.c : E) ≠ 0 := neg_ne_zero.2 A.c_ne
  have hu : IsUnit (A.H n).det := (A.det_ne n).isUnit
  have hD : Dm A n = (-(A.c : E))⁻¹ • A.H n := by
    rw [H_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hermStar_apply, show (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n from H_cj A n, hD]
  rw [smul_mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_smul]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

private def βS (S : Setup A n p) : S.G.Cˣ :=
  (⟨Dm A n, Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)⁻¹, by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (dg_ne A n i), by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (dg_ne A n i)⟩ : (Matrix (Fin n) (Fin n) E)ˣ)

private lemma hU (A : Arith E) (n : ℕ) : IsUnit (Dm A n) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  exact (Finset.prod_ne_zero_iff.2 fun i _ => dg_ne A n i).isUnit

private lemma βS_sym (S : Setup A n p) : sh S.G (βS S : S.G.Cˣ) = (βS S : S.G.Cˣ) := by
  have h := D_star A n (Dm A n)
  have hD : (Dm A n).map (cj E) = Dm A n := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact dg_cj A n i
  rw [hD, Matrix.diagonal_transpose] at h
  exact (hU A n).mul_right_inj.1 h

private lemma βS_pos (S : Setup A n p) (v : InfinitePlace S.G.F) (x : Fin S.G.n → ℂ) (hx : x ≠ 0) :
    (sigPosH (S.G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((S.G.gram v * S.G.psi v (((βS S)⁻¹ : S.G.Cˣ) : S.G.C)) *ᵥ x)).re) ∧
      (sigPosH (S.G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((S.G.gram v * S.G.psi v (((βS S)⁻¹ : S.G.Cˣ) : S.G.C)) *ᵥ x)).re < 0) := by
  have hs : sigPosH (S.G.gram_herm v) = sigPos (A.herm n) v.embedding := rfl
  have hf : S.G.gram v * S.G.psi v (((βS S)⁻¹ : S.G.Cˣ) : S.G.C) = Matrix.diagonal fun _ => -v.embedding (A.c : E) :=
    form_eq A n v.embedding
  have hP := sum_pos' hx
  rw [hf, re_form, hs, Complex.neg_re]
  by_cases hm : InfinitePlace.mk v.embedding = InfinitePlace.mk A.τ₀
  · have hc := c_re_neg A v.embedding hm
    have h1' := ((S.sig v.embedding).1 hm).1
    exact ⟨fun _ => mul_pos (neg_pos.2 hc) hP, fun h => absurd h1' h⟩
  · have hc := A.c_pos v.embedding hm
    have h0 := ((S.sig v.embedding).2 hm).1
    refine ⟨fun h => ?_, fun _ => mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hP⟩
    rw [h0] at h
    exact absurd h (by norm_num)

private lemma sim_comm {Y Z : Matrix (Fin n) (Fin n) E} {s : E} (hs : s ≠ 0) (h : Y * Z = s • 1) : Z * Y = s • 1 := by
  have h1 : Y * (s⁻¹ • Z) = 1 := by rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  rw [smul_mul_assoc] at h2
  calc Z * Y = s • (s⁻¹ • (Z * Y)) := by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
    _ = s • 1 := by rw [h2]

private lemma alg_mat (q : ℚ) : algebraMap ℚ (Matrix (Fin n) (Fin n) E) q = algebraMap ℚ E q • (1 : Matrix (Fin n) (Fin n) E) := by
  rw [Algebra.algebraMap_eq_smul_one, algebraMap_smul]

private lemma mem_iff (S : Setup A n p) (y : GL (Fin n) E × ℚˣ) : y ∈ GlobalTheory.LKCx.grp S.G (βS S) ↔ y ∈ Gam0 E n := by
  have hs (q : ℚˣ) : algebraMap ℚ E q ≠ 0 := by simp
  have key : (y.1.val * Dm A n) * (hermStar (A.H n) (A.det_ne n) y.1.val).unop =
      y.1.val * (y.1.val.map (cj E))ᵀ * Dm A n := by
    rw [Matrix.mul_assoc, D_star, Matrix.mul_assoc]
  have hg : y ∈ GlobalTheory.LKCx.grp S.G (βS S) ↔
      (y.1.val * (y.1.val.map (cj E))ᵀ = algebraMap ℚ E y.2 • (1 : Matrix (Fin n) (Fin n) E)) ∧ 0 < (y.2 : ℚ) := by
    refine and_congr_left' ?_
    change (y.1.val * Dm A n) * (hermStar (A.H n) (A.det_ne n) y.1.val).unop = algebraMap ℚ (Matrix (Fin n) (Fin n) E) y.2 * Dm A n ↔ _
    rw [key, alg_mat]
    exact (hU A n).mul_left_inj
  have hG : y ∈ Gam0 E n ↔
      ((y.1.val.map (cj E))ᵀ * y.1.val = algebraMap ℚ E y.2 • (1 : Matrix (Fin n) (Fin n) E)) ∧ 0 < (y.2 : ℚ) := Iff.rfl
  rw [hg, hG]
  exact and_congr_left' ⟨sim_comm (hs _), sim_comm (hs _)⟩

private noncomputable def xOf {S : Setup A n p} (T : Tr S) : (AfP p ⊗[ℚ] S.G.C)ˣ :=
  Units.map (RingHom.toMonoidHom T.μ.symm.toRingHom) (GeneralLinearGroup.map T.Φ T.a)

private noncomputable def xv {S : Setup A n p} (T : Tr S) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E := (xOf T).val

private noncomputable def xiv {S : Setup A n p} (T : Tr S) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E := ((xOf T)⁻¹).val

private lemma traceMap_unipotent {S : Setup A n p} (T : Tr S) : T.μ (xv T) = T.a.val.map T.Φ :=
  T.μ.apply_symm_apply _

private lemma mu_xi {S : Setup A n p} (T : Tr S) : T.μ (xiv T) = (T.a⁻¹).val.map T.Φ :=
  T.μ.apply_symm_apply _

private lemma mu_one {S : Setup A n p} (T : Tr S) (M : Matrix (Fin n) (Fin n) E) :
    T.μ ((1 : AfP p) ⊗ₜ[ℚ] M) = M.map fun e => (1 : AfP p) ⊗ₜ[ℚ] e := by
  ext i k
  exact T.mu 1 M i k

private lemma triv_xOf_of_muStar (hM : MuStar) {S : Setup A n p} (T : Tr S) : Triv S.G (AfP p) (βS S : S.G.Cˣ) (xOf T) 1 := by
  have hst := hM (AfP p) E A n T.μ T.mu (xv T)
  rw [traceMap_unipotent] at hst
  have hD : (Dm A n).map (fun e => (1 : AfP p) ⊗ₜ[ℚ] e) =
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E)) := by
    ext i k
    by_cases h : i = k
    · subst h; simp
    · simp [h]
  have h0 := congrArg (fun M => M.map T.Φ) T.iso.1
  simp only [Matrix.map_mul] at h0
  have h1 : ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ *
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E)) * T.a.val.map T.Φ = 1 := by
    have e1 : ((T.a.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ).map T.Φ = ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ := by
      ext i k
      exact T.Φ_conj _
    have e2 : (Matrix.diagonal fun i => algebraMap E (Af E) ((A.dg n i : 𝓞 E) : E)).map T.Φ =
        Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E)) := by
      ext i k
      by_cases h : i = k
      · subst h; simp [T.Φ_E]
      · simp [h]
    rw [e1, e2, Matrix.map_one _ (map_zero _) (map_one _)] at h0
    exact h0
  have h2 : T.a.val.map T.Φ * (((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ *
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E))) = 1 := mul_eq_one_comm.1 h1
  have e : xv T * ((1 : AfP p) ⊗ₜ[ℚ] Dm A n) * (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (xv T)).unop = 1 := by
    apply T.μ.injective
    rw [map_mul, map_mul, map_one, traceMap_unipotent, mu_one, hD, Matrix.mul_assoc, hst]
    exact h2
  exact e.trans (map_one _).symm

private lemma emb_eq {S : Setup A n p} (T : Tr S) (hx : Triv S.G (AfP p) (βS S : S.G.Cˣ) (xOf T) 1) (y : GL (Fin n) E × ℚˣ)
    (h : y ∈ GlobalTheory.LKCx.grp S.G (βS S)) (h' : y ∈ Gam0 E n) :
    GlobalTheory.LKCx.toAfF S.G (βS S) (xOf T) 1 hx ⟨y, h⟩ = T.j (rat ⟨y, h'⟩) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply T.μ.injective
    refine Eq.trans ?_ (T.j_mx (rat ⟨y, h'⟩)).symm
    change T.μ (xv T * ((1 : AfP p) ⊗ₜ[ℚ] y.1.val) * xiv T) = _
    rw [map_mul, map_mul, traceMap_unipotent, mu_xi, mu_one, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext i k
    exact (T.Φ_E _).symm
  · apply Units.ext
    refine Eq.trans ?_ (T.j_sim (rat ⟨y, h'⟩)).symm
    exact RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (AfP p)) (T.ρ.comp (algebraMap ℚ AfQ))) _

end
theorem UpperTheory.Gal.W2.Seed.pStdForm2 :
    MuStar → StdForm2 := by
  intro hM E _ _ _ A n p _ S T
  have hx := triv_xOf_of_muStar hM T
  refine ⟨⟨βS S, βS_sym S, ⟨xOf T, 1, hx⟩, βS_pos S⟩, xOf T, hx, fun y => mem_iff S y, fun y h h' => emb_eq T hx y h h'⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.W2.Seed

def TyLev.kerK {X M : Type} [Group X] [Group M] (T : TyLev X M) : Subgroup X :=
  ((T.ψ.comp ((T.L.pr.comp T.K.subtype).codRestrict T.J fun k => T.fact.2 k k.2)).ker).map T.K.subtype

theorem TyLev.mem_kerK {X M : Type} [Group X] [Group M] (T : TyLev X M) (k : X) :
    k ∈ T.kerK ↔ ∃ hk : k ∈ T.K, T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩ = 1 :=
  ⟨fun ⟨y, hy, e⟩ => e ▸ ⟨y.2, hy⟩, fun ⟨hk, h⟩ => ⟨⟨k, hk⟩, h, rfl⟩⟩

theorem TyLev.triv_of_le {X M : Type} [Group X] [Group M] (T : TyLev X M) {K : Subgroup X} (h : K ≤ T.kerK) : T.Triv K :=
  ⟨fun k hk => ((T.mem_kerK k).1 (h hk)).1, fun k hk _ => ((T.mem_kerK k).1 (h hk)).2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

theorem th_eq (F : Frame S) : F.th = CertificateRingHomMap.th :=
  MonoidHom.ext fun g => Subtype.ext (Prod.ext (Units.ext (F.th_mat g)) (F.th_sim g))

def FacEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (hc : LocComm) (w : Spl E p), IsFac F w (fac F.tr hc w) ∧ ∀ L, IsFac F w L → L = fac F.tr hc w

def LevSec : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (S₀ : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)), (∀ u ∈ S₀, (p : 𝓞 E) ∉ u.asIdeal) →
  (∀ k ∈ lev S₀ Kw, T.sec (T.j k) ∈ lev S₀ Kw) ∧
  ∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) → (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w (n := n)) →
    (∀ u ∈ S₀, (1 : GLw n u) ∈ Kw u) → k ∈ lev S₀ Kw

def IsCongGrp (N : ℕ) (w : Plc E) (K : Subgroup (GLw n w)) : Prop := ∀ y, y ∈ K ↔ Cong1 N w y ∧ Cong1 N w y⁻¹

def CongGrpEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), 0 < N → ∀ w : Plc E, ∃ K : Subgroup (GLw n w),
  IsCongGrp N w K ∧ IsOpen (K : Set (GLw n w)) ∧ IsCompact (K : Set (GLw n w)) ∧ K ≤ KGL w (n := n) ∧
    (∀ a ∈ KGL w (n := n), ∀ y, a * y * a⁻¹ ∈ K ↔ y ∈ K) ∧ ((N : 𝓞 E) ∈ w.asIdeal → K ≤ Iw n w) ∧ Iw n w ≤ KGL w (n := n)

def CongConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ) (w : Plc E) (g : GUf E n), sim g = 1 →
  Cong1 N w (comp w g)⁻¹ → Cong1 N (CertificateRingHomMap.cj w) (comp (CertificateRingHomMap.cj w) g)

def KNFact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (w : Spl E p) (L : Loc S.G.GAf (GLw n w.1)), IsFac F w L → ∀ q : ℕ, q.Prime → A.Good q → (q : 𝓞 E) ∈ w.1.asIdeal →
  ∀ N : ℕ, 0 < N → ∀ K : Subgroup (GLw n w.1), IsCongGrp N w.1 K → L.Fact (S.L.KN N) K

def SiteFact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (x : E), Gen A x → ∀ (N : Lv p) (w : Spl E p) (σ : Site S N w.1) (L : Loc S.G.GAf (GLw n w.1)), IsFac F w L →
  L.Fact σ.K₀ (KGL w.1 (n := n))

def CuspTh : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (σ : SmIrr (GLw n w)),
  ∃ σ' : SmIrr (GLw n w), ∃ e : σ.V ≃ₗ[ℂ] σ'.V, (∀ (g g' : GLw n w) v, g'.val = (g⁻¹).valᵀ → σ'.ρ g' (e v) = e (σ.ρ g v)) ∧
    (GlobalTheory.SmGL.IsCuspidal σ'.ρ → GlobalTheory.SmGL.IsCuspidal σ.ρ)

def Denom : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (h : G.GAf),
  ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ ∀ v ∈ LaHat D, c • L.actG h v ∈ LaHat D

def CenFacts : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), 0 < n → ∀ x : E, Gen A x →
  ∀ q : ℕ, q.Prime → A.SplitK q → ∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal → ∀ z : GUf E n, IsCen x w z →
  (∀ g, z * g = g * z) ∧ ∀ u : Plc E, (q : 𝓞 E) ∉ u.asIdeal → comp u z = 1

def StabKer : Prop := ForData fun _ _ _ _ _ _ _ _ S F _ _ _ _ V r _ _ _ Ty => ∀ k, Stab F V k → k ∈ S.L.KN r → k ∈ Ty.kerK

def SeenShape : Prop := ForData fun E _ _ _ _ n p _ S F x U _ _ V r W N L Ty => ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ →
  g.K ≤ Ty.kerK ∧ ((IsDeckM g ∧ g.h ∈ Ty.kerK ∧ θ = 1) ∨
  ∃ (w : Spl E p) (t : GLw n w.1) (z : GUf E n) (i : ℕ) (B : Multiset ℂˣ), Free V w.1 ∧ (∀ u ∈ W, Apart w.1 u.1) ∧ i ≤ n ∧ IsT w.1 i t ∧
    IsCen x w.1 z ∧ SatU U w.1 B ∧ (∀ u : Plc E, (p : 𝓞 E) ∈ u.asIdeal → comp u z = 1) ∧
    g.h⁻¹ = (L w).loc t⁻¹ * F.j (z ^ i)⁻¹ ∧ Ty.Cen (F.j (z ^ i)⁻¹) ∧ (∀ u ∈ W, (L u).pr g.h = 1) ∧ (L w).Fact g.K (KGL w.1 (n := n)) ∧
    θ = (idx g : ℂ) * (satEig (Ideal.absNorm w.1.asIdeal) n B i * (((V.κ.val w.1 : ℂˣ) : ℂ)⁻¹) ^ i))

def SeenActs : Prop := ForData fun _ _ _ _ _ _ _ _ S F _ _ _ _ V r _ N _ Ty => ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ →
  (∀ a, g.fn a ≠ 0 → ∃ k ∈ Ty.K, g.h * k * a ∈ Ty.K) ∧
  (IsDeckM g → g.h ∈ Ty.kerK → Ty.Acts g.fn 1 1) ∧
  ∀ (M' : Type) [Group M'] (L' : Loc S.G.GAf M') (Kw : Subgroup M') (t : M') (z : S.G.GAf), L'.Fact Ty.K Kw → L'.Fact g.K Kw → Ty.L.Apart L' →
    Ty.Cen z → g.h⁻¹ = L'.loc t * z → Ty.Acts g.fn (idx g) g.h⁻¹

def ActsConv : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h : X), T.Acts ψ c h →
  conv T.K₀ ψ (T.tf 1) = c • T.tf h ∧ ∀ (c' : ℂ) (h' : X), T.L.pr h' = 1 →
    conv T.K₀ ψ (c' • T.tf h') = (c * c') • conv T.K₀ (T.tf h) (T.tf h')

def TEig : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E)
  (Up : Plc E → Prop) (V : Vec x U w₀ Up) (w : Plc E) (hw : IsSplitAt w), Free V w → ∀ (i : ℕ), i ≤ n → ∀ t, IsT w i t → ∀ z, IsCen x w z →
  ∀ B, SatU U w B → ∀ g : GUf E n,
    ∑ᶠ y : GLw n w ⧸ KGL w (n := n), dosetInd ℂ (KGL w (n := n)) t⁻¹ y.out • V.Φ (CertificateRingHomMap.th (g * (z ^ i)⁻¹ * CertificateRingHomMap.loc hw y.out)) =
      (satEig (Ideal.absNorm w.asIdeal) n B i * (((V.κ.val w : ℂˣ) : ℂ)⁻¹) ^ i) • V.Φ (CertificateRingHomMap.th g)

def PhiTy : Prop := ForData fun E _ _ _ _ n p _ _ F _ _ _ _ V _ _ _ _ Ty =>
  (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) ≠ 0 ∧ Ty.IsTy (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) ∧
  (∀ g : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g ∈ KGL w (n := n)) → V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j g))) = V.Φ (CertificateRingHomMap.th g)) ∧
  ∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) → (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w (n := n)) →
    ∀ g, V.Φ (CertificateRingHomMap.th (g * k)) = V.Φ (CertificateRingHomMap.th g)

end UpperTheory.Gal.W2.Seed
end
end

