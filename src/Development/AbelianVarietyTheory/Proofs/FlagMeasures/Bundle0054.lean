module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeOfSqueezedBetweenNatMultiples
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.glue_latt_isLattice {E : Type} [Field E] [NumberField E] (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (hN : N ≠ 0)
    (hlow : ∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ)
    (hup : ∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) : Submodule.IsLattice E Γ := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
    ((N : E)⁻¹ • (LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)))
  have hle : Γ ≤ LinearMap.range f := by
    intro x hx
    refine ⟨fun i => ⟨(N : E) * x i, hup x hx i⟩, ?_⟩
    ext i
    change (N : E)⁻¹ * ((N : E) * x i) = x i
    rw [← mul_assoc, inv_mul_cancel₀ hNE, one_mul]
  refine ⟨?_, ?_⟩
  · rw [← Submodule.map_comap_eq_self hle]
    exact (IsNoetherian.noetherian _).map f
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalCommonStabiliserBlockUnitriangularOnFrame
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocPattern
open GlobalTheory.HL.Eichler

section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem zh_split (l : Fin (r + 2)) (hl : S.D l ≠ 0) (x y : Fin (r + 1))
    (hxy : ((x : ℕ) < l ∧ (l : ℕ) ≤ y) ∨ ((y : ℕ) < l ∧ (l : ℕ) ≤ x)) : S.Zh x y = 0 := by
  have hZ : ∀ a b : Fin (r + 1), S.Zh a b = ptEntryL S.w.blocks a b * (-1) ^ (r - (b : ℕ)) :=
    fun a b => S.relevant a b
  have hA : ∀ a : Fin (r + 1), (a : ℕ) < l → GlobalTheory.FrameBasic.sig S.w.blocks a < l := by
    intro a ha
    by_contra hc
    push_neg at hc
    apply hl
    unfold Frames.D lead
    apply Matrix.det_eq_zero_of_row_eq_zero (⟨a, ha⟩ : Fin l)
    intro j
    simp only [Matrix.submatrix_apply]
    rw [hZ]
    have hj := j.2
    have : ((Fin.castLE (Nat.lt_succ_iff.mp l.2) j : Fin (r + 1)) : ℕ) ≠
        GlobalTheory.FrameBasic.sig S.w.blocks (Fin.castLE (Nat.lt_succ_iff.mp l.2) (⟨a, ha⟩ : Fin l) : Fin (r + 1)) := by
      simp only [Fin.coe_castLE]; omega
    rw [GlobalTheory.FrameBasic.entry_zero _ _ _ this, zero_mul]
  rw [hZ]
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [GlobalTheory.FrameBasic.entry_zero _ _ _ (by have := hA x h1; omega), zero_mul]
  · rw [GlobalTheory.FrameBasic.entry_zero _ _ _ ?_, zero_mul]
    intro he
    have h3 := hA y h1
    rw [he, GlobalTheory.FrameBasic.sig_sig] at h3
    omega

theorem m_zero [IsNonarchimedeanLocalField F] [CharZero F]
    (m m' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hm' : (∀ i j, j < i → m' i j = 0) ∧ (∀ i, m' i i = 1))
    (heq : cT L m * S.Zh * m' = S.Zh) (l : Fin (r + 2)) (hl : S.D l ≠ 0) (a b : Fin (r + 1))
    (ha : (a : ℕ) < l) (hb : (l : ℕ) ≤ b) : m a b = 0 := by
  obtain ⟨-, -, -, hU, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hU' : IsUnit S.Zh.det := hU
  have hbt : m'.BlockTriangular id := by
    intro i j hij; exact hm'.1 i j hij
  have hdet : IsUnit m'.det := by
    rw [Matrix.det_of_upperTriangular hbt]; simp [hm'.2]
  letI := Matrix.invertibleOfIsUnitDet m' hdet
  have hN : (m'⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have h1 : cT L m * S.Zh = S.Zh * m'⁻¹ := by
    calc cT L m * S.Zh = cT L m * S.Zh * m' * m'⁻¹ := by
          rw [Matrix.mul_assoc (cT L m * S.Zh) m', Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = S.Zh * m'⁻¹ := by rw [heq]
  let v : Fin (r + 1) → E := fun x => if (x : ℕ) < l then L.cj (m x b) else 0
  have hv : Matrix.vecMul v S.Zh = 0 := by
    funext y
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hy : (y : ℕ) < l
    · have h2 := congrFun (congrFun h1 b) y
      rw [Matrix.mul_apply, Matrix.mul_apply] at h2
      have h3 : ∑ z, S.Zh b z * m'⁻¹ z y = 0 := Finset.sum_eq_zero fun z _ => by
        by_cases hz : (z : ℕ) ≤ y
        · rw [zh_split S l hl b z (Or.inr ⟨by omega, hb⟩), zero_mul]
        · rw [hN (show y < z from Fin.lt_def.2 (by omega)), mul_zero]
      rw [h3] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [v, cT]
      split_ifs with hx
      · rfl
      · simp [zh_split S l hl x y (Or.inr ⟨hy, by omega⟩)]
    · refine Finset.sum_eq_zero fun x _ => ?_
      simp only [v]
      split_ifs with hx
      · rw [zh_split S l hl x y (Or.inl ⟨hx, by omega⟩), mul_zero]
      · rw [zero_mul]
  have hv0 : v = 0 := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
    (hv.trans (Matrix.zero_vecMul _).symm)
  have := congrFun hv0 a
  simp only [v, if_pos ha, Pi.zero_apply] at this
  exact (map_eq_zero_iff L.cj L.cj.injective).1 this

end Local

section Scal
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]

theorem ab_one (c : Kˣ) (n : ℕ) : algebraMap K B ((c : K) ^ n) * algebraMap K B (((c⁻¹ ^ n : Kˣ)) : K) = 1 := by
  rw [← map_mul, Units.val_pow_eq_pow_val, ← mul_pow, Units.mul_inv, one_pow, map_one]

theorem ba_one (c : Kˣ) (n : ℕ) : algebraMap K B (((c⁻¹ ^ n : Kˣ)) : K) * algebraMap K B ((c : K) ^ n) = 1 := by
  rw [mul_comm, ab_one]

end Scal

section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

theorem f_loc (a : Fin (r + 1)) : (G.S p).f a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) •
      A.bc p (G.f a) := by
  rw [← G.f_eq p a, smul_smul, ba_one, one_smul]

theorem f'_loc (a : Fin (r + 1)) : (G.S p).f' a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) •
      A.bc p (G.f' a) := by
  rw [← G.f'_eq p a, smul_smul, ba_one, one_smul]

theorem zh_loc (a b : Fin (r + 1)) : (G.S p).Zh a b =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (b : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) *
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) *
      (A.loc p).ιE (G.Zh a b) := by
  show hf (A.L p) (G.S p).Hm ((G.S p).f' b) ((G.S p).f a) = _
  rw [f_loc, f'_loc, hf_smul_l, hf_smul_r, AlgEquiv.commutes, G.Hm_eq p,
    (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)]
  simp only [GFrames.Zh, Matrix.of_apply]
  ring

theorem D_ne (l : Fin (r + 2)) (h : G.D l ≠ 0) : (G.S p).D l ≠ 0 := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  set e : Fin l → Fin (r + 1) := Fin.castLE (Nat.lt_succ_iff.mp l.2) with he
  let d : Fin l → (A.loc p).Ep := fun i =>
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (e i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp)
  have hsub : (G.S p).Zh.submatrix e e =
      Matrix.diagonal d * (G.Zh.submatrix e e).map (A.loc p).ιE * Matrix.diagonal d := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, zh_loc, d]
    ring
  have hmap : ((G.Zh.submatrix e e).map (A.loc p).ιE).det = (A.loc p).ιE (G.D l) :=
    (RingHom.map_det _ _).symm
  have hD : (G.S p).D l = (∏ i, d i) * (A.loc p).ιE (G.D l) * (∏ i, d i) := by
    show ((G.S p).Zh.submatrix e e).det = _
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hmap]
  have hu : IsUnit (∏ i, d i) := by
    rw [IsUnit.prod_univ_iff]
    intro i
    exact (Units.isUnit _).map _
  rw [hD]
  intro h0
  rw [hu.mul_left_eq_zero, hu.mul_right_eq_zero] at h0
  exact h ((map_eq_zero_iff _ (A.loc p).ιE.injective).1 h0)

end Global

theorem local_pattern : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV), h ∈ (G.S p).St → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep, (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) → G.D l = 0) → s i j = if i = j then 1 else 0) ∧ (∀ j, h (A.bc p (G.f j)) = ∑ i, s i j • A.bc p (G.f i)) ∧ ((∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p) → h ∈ (G.S p).K0 → IsIntM (A.L p) s) := by
  intro F E _ _ _ _ _ sig A r k G p h hh
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hN1, hN2, -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto (A.L p) r k (G.S p)
  obtain ⟨m, hm, hmf⟩ := hN1 h hh.1
  obtain ⟨m', hm', hmf'⟩ := hN2 h hh.2
  have heq : cT (A.L p) m * (G.S p).Zh * m' = (G.S p).Zh :=
    ((GlobalTheory.HL.FrameStab.stab_eq (A.L p) r k (G.S p)).2 m m' hm hm').2 ⟨h, hh, hmf, hmf'⟩
  refine ⟨fun i j => algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (j : ℕ))) * m i j *
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp),
    ?_, ?_, ?_⟩
  · intro i j hij
    beta_reduce
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have hex : ∃ l : Fin (r + 2), (i : ℕ) < l ∧ (l : ℕ) ≤ j ∧ G.D l ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hij ⟨hlt, fun l h1 h2 => hc l h1 h2⟩
      obtain ⟨l, h1, h2, h3⟩ := hex
      rw [if_neg hlt.ne, m_zero (G.S p) m m' hm' heq l (D_ne G p l h3) i j h1 h2]
      simp
    · rw [if_pos rfl, hm.2, mul_one, ab_one]
    · rw [if_neg hgt.ne', hm.1 i j hgt]
      simp
  · intro j
    beta_reduce
    rw [← G.f_eq p j, map_smul, hmf j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← G.f_eq p i, smul_smul, smul_smul, mul_assoc (_ * m i j), ba_one, mul_one]
  · rintro ⟨u, hu⟩ hK i j
    have hli : LinearIndependent (A.loc p).Ep (G.S p).f :=
      (GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)).1.comp Sum.inl Sum.inl_injective
    have hmem : h ((G.S p).f j) ∈ Submodule.span (A.L p).O (Set.range (G.S p).f) := by
      have h1 : h • Submodule.span (A.L p).O (Set.range (G.S p).f) =
          Submodule.span (A.L p).O (Set.range (G.S p).f) := hK.1.2
      rw [← h1]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
    have hb' : ∑ i, ((b i : (A.L p).O) : (A.loc p).Ep) • (G.S p).f i = h ((G.S p).f j) := by
      rw [← hb]
      exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
    have hmb : m i j = b i := by
      have := Fintype.linearIndependent_iff.1 hli (fun i => ((b i : (A.L p).O) : (A.loc p).Ep) - m i j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, hb', hmf j, sub_self])
      exact (sub_eq_zero.1 (this i)).symm
    have hO : ∀ (y : 𝒪[(A.loc p).Fp]) (n : ℕ),
        algebraMap (A.loc p).Fp (A.loc p).Ep ((y : (A.loc p).Fp) ^ n) ∈ (A.L p).O := by
      intro y n
      rw [map_pow]
      refine pow_mem (((A.L p).O_def _).2 ?_) n
      rw [show (y : (A.loc p).Fp) = algebraMap 𝒪[(A.loc p).Fp] (A.loc p).Fp y from rfl,
        ← IsScalarTower.algebraMap_apply]
      exact isIntegral_algebraMap
    have hinv : (((G.c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = (((u⁻¹ : (𝒪[(A.loc p).Fp])ˣ) : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) := by
      rw [Units.val_inv_eq_inv_val, ← hu]
      symm
      apply eq_inv_of_mul_eq_one_left
      exact congrArg (fun x : 𝒪[(A.loc p).Fp] => (x : (A.loc p).Fp)) (Units.inv_mul u)
    refine Subring.mul_mem _ (Subring.mul_mem _ ?_ (hmb ▸ (b i).2)) ?_
    · rw [← hu]; exact hO u _
    · rw [Units.val_pow_eq_pow_val, hinv]; exact hO _ _

end GlobalTheory.HL.LocPattern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeBetweenScaledStandardLattices
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

section general

variable {R : Type} [CommRing R] {O : Subring R} {n : ℕ}

theorem smul_mem_of_mem' (Λ : Submodule O (Fin n → R)) {c : R} (hc : c ∈ O) {x : Fin n → R}
    (hx : x ∈ Λ) : c • x ∈ Λ := by
  have := Λ.smul_mem (⟨c, hc⟩ : O) hx
  simpa [Subring.smul_def] using this

theorem exists_nat_smul_mem (Λ : Submodule O (Fin n → R))
    (hd : ∀ y : R, ∃ m : ℕ, m ≠ 0 ∧ (m : R) * y ∈ O) {x : Fin n → R}
    (hx : x ∈ Submodule.span R (Λ : Set (Fin n → R))) : ∃ m : ℕ, m ≠ 0 ∧ (m : R) • x ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem ..)

theorem exists_nat_between (Λ : Submodule O (Fin n → R)) (hfg : Λ.FG)
    (hsp : Submodule.span R (Λ : Set (Fin n → R)) = ⊤)
    (hd : ∀ y : R, ∃ m : ℕ, m ≠ 0 ∧ (m : R) * y ∈ O) :
    ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → R, (∀ i, v i ∈ O) → (m : R) • v ∈ Λ) ∧
      ∀ v ∈ Λ, ∀ i, (m : R) * v i ∈ O := by
  choose md hmd0 hmd using hd
  obtain ⟨S, hS⟩ := hfg

  set m1 : ℕ := ∏ s ∈ S, ∏ i, md (s i) with hm1
  have hm10 : m1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun i _ => hmd0 _
  have hup : ∀ v ∈ Λ, ∀ i, (m1 : R) * v i ∈ O := by
    intro v hv
    rw [← hS] at hv
    induction hv using Submodule.span_induction with
    | mem s hs =>
      intro i
      have hdvd : md (s i) ∣ m1 :=
        (Finset.dvd_prod_of_mem (fun j => md (s j)) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun t : Fin n → R => ∏ j, md (t j)) hs)
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, Nat.cast_mul, mul_comm (md (s i) : R), mul_assoc]
      exact O.mul_mem (natCast_mem O k) (hmd _)
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; simpa [mul_add] using O.add_mem (hx i) (hy i)
    | smul a x _ hx =>
      intro i
      have : (m1 : R) * (a • x) i = (a : R) * ((m1 : R) * x i) := by
        simp [Subring.smul_def]; ring
      rw [this]
      exact O.mul_mem a.2 (hx i)

  have hsingle : ∀ i : Fin n, ∃ m : ℕ, m ≠ 0 ∧ (m : R) • (Pi.single i 1 : Fin n → R) ∈ Λ := fun i =>
    exists_nat_smul_mem Λ (fun y => ⟨md y, hmd0 y, hmd y⟩) (by rw [hsp]; exact Submodule.mem_top)
  choose ms hms0 hms using hsingle
  set m2 : ℕ := ∏ i, ms i with hm2
  have hm20 : m2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hms0 i
  have hsing2 : ∀ i, (m2 : R) • (Pi.single i 1 : Fin n → R) ∈ Λ := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem ms (Finset.mem_univ i)
    rw [← hm2] at hk
    rw [hk, Nat.cast_mul, mul_comm, ← smul_smul]
    exact smul_mem_of_mem' Λ (natCast_mem O k) (hms i)
  have hlow : ∀ v : Fin n → R, (∀ i, v i ∈ O) → (m2 : R) • v ∈ Λ := by
    intro v hv
    have h : (m2 : R) • v = ∑ i, v i • ((m2 : R) • (Pi.single i 1 : Fin n → R)) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [h]
    exact Λ.sum_mem fun i _ => smul_mem_of_mem' Λ (hv i) (hsing2 i)
  refine ⟨m1 * m2, mul_ne_zero hm10 hm20, fun v hv => ?_, fun v hv i => ?_⟩
  · have : ((m1 * m2 : ℕ) : R) • v = (m1 : R) • ((m2 : R) • v) := by push_cast; rw [smul_smul]
    rw [this]
    exact smul_mem_of_mem' Λ (natCast_mem O m1) (hlow v hv)
  · have : ((m1 * m2 : ℕ) : R) * v i = (m2 : R) * ((m1 : R) * v i) := by push_cast; ring
    rw [this]
    exact O.mul_mem (natCast_mem O m2) (hup v hv i)

end general

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem lat_between (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (Λ : Submodule (A.L p).O (Fin n → (A.loc p).Ep)) (hΛ : IsLat (A.L p) Λ)
    (hd : ∀ y : (A.loc p).Ep, ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O) :
    ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (m : (A.loc p).Ep) • v ∈ Λ) ∧
      ∀ v ∈ Λ, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O :=
  exists_nat_between Λ hΛ.1 hΛ.2 hd

end GlobalTheory.HL.Glue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeLeCompletionGluedLattice
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem local_le_lat_of_approx {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep))
    (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ)
    (hΓ : ∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p)
    (hN : ∀ p (v : Fin n → (A.loc p).Ep), (∀ i, v i ∈ (A.L p).O) → (N : (A.loc p).Ep) • v ∈ Λ p)
    (happ : ∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite →
      ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = (N : (A.loc p).Ep) * o) :
    ∀ p, Λ p ≤ A.lat p Γ := by
  intro p v hv
  have hsingle : ∀ i : Fin n, ((N : E) • (Pi.single i 1 : Fin n → E)) ∈ Γ := by
    intro i
    rw [hΓ]
    intro q
    have h1 : A.bc q ((N : E) • (Pi.single i 1 : Fin n → E)) =
        (N : (A.loc q).Ep) • (Pi.single i 1 : Fin n → (A.loc q).Ep) := by
      funext j
      simp only [Places.bc, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [h1]
    apply hN
    intro j
    by_cases h : j = i
    · subst h; simp [Subring.one_mem]
    · simp [Pi.single_apply, h, Subring.zero_mem]
  have hint : ∀ w : Fin n → (A.loc p).Ep, (∀ i, w i ∈ (A.L p).O) →
      (N : (A.loc p).Ep) • w ∈ A.lat p Γ := by
    intro w hw
    have hw' : (N : (A.loc p).Ep) • w =
        ∑ i, (⟨w i, hw i⟩ : (A.L p).O) • A.bc p ((N : E) • (Pi.single i 1 : Fin n → E)) := by
      funext j
      simp [Places.bc, Subring.smul_def, Pi.single_apply, Finset.sum_apply, mul_comm]
      simp [apply_ite (A.loc p).ιE, mul_ite, Finset.sum_ite_eq, mul_comm]
    rw [hw']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle i, rfl⟩)
  have hfin : ∀ i, {q | (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q ∉ (A.L q).O}.Finite := by
    intro i
    apply (Set.finite_singleton p).subset
    intro q hq
    by_contra h
    apply hq
    rw [Pi.single_eq_of_ne h]
    exact (A.L q).O.zero_mem
  choose x hx using fun i => happ _ (hfin i)
  choose o ho hxo using hx
  have hbc : ∀ q, A.bc q (fun i => x i) =
      (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) + (N : (A.loc q).Ep) • (fun i => o i q) := by
    intro q
    funext i
    have h2 := hxo i q
    simp only [Places.bc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h2]
    ring
  have hX : (fun i => x i) ∈ Γ := by
    rw [hΓ]
    intro q
    rw [hbc q]
    refine (Λ q).add_mem ?_ (hN q _ fun i => ho i q)
    by_cases hq : q = p
    · subst hq
      simpa using hv
    · have h3 : (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) = 0 := by
        funext i
        simp [Pi.single_eq_of_ne hq]
      rw [h3]
      exact (Λ q).zero_mem
  have hv' : v = A.bc p (fun i => x i) - (N : (A.loc p).Ep) • (fun i => o i p) := by
    rw [hbc p]
    funext i
    simp
  rw [hv']
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, hX, rfl⟩) (hint _ fun i => ho i p)

end GlobalTheory.HL.Glue
end

