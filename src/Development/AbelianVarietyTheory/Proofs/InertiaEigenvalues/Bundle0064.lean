module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLatComap
section
noncomputable section
namespace GlobalTheory.LatticeComap
open GlobalTheory.PhiGam

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module (LaurentSeries k) V]
  [Module (PowerSeries k) V] [IsScalarTower (PowerSeries k) (LaurentSeries k) V]

theorem exists_pow_smul_mem {N : Submodule (PowerSeries k) V}
    (hN : Submodule.span (LaurentSeries k) (N : Set V) = ⊤) (x : V) :
    ∃ m : ℕ, ((PowerSeries.X : PowerSeries k) ^ m) • x ∈ N := by
  have hx : x ∈ Submodule.span (LaurentSeries k) (N : Set V) := by rw [hN]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0, by simpa using hy⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m1, h1⟩ := hy
    obtain ⟨m2, h2⟩ := hz
    refine ⟨m1 + m2, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact N.smul_mem _ h1
    · rw [pow_add, mul_smul]; exact N.smul_mem _ h2
  | smul a y _ hy =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨⟨p, s⟩, hps⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : PowerSeries k)) a
    obtain ⟨j, hj⟩ := s.2
    have hj' : (PowerSeries.X : PowerSeries k) ^ j = (s : PowerSeries k) := hj
    have hps' : a * algebraMap (PowerSeries k) (LaurentSeries k) (s : PowerSeries k) =
        algebraMap (PowerSeries k) (LaurentSeries k) p := hps
    have key : ((PowerSeries.X : PowerSeries k) ^ j) • a • y = p • y := by
      rw [← algebraMap_smul (LaurentSeries k) ((PowerSeries.X : PowerSeries k) ^ j) (a • y), smul_smul, hj',
        mul_comm, hps', algebraMap_smul]
    refine ⟨m + j, ?_⟩
    rw [pow_add, mul_smul, key, smul_comm]
    exact N.smul_mem _ hm

variable {W : Type} [AddCommGroup W] [Module (LaurentSeries k) W]
  [Module (PowerSeries k) W] [IsScalarTower (PowerSeries k) (LaurentSeries k) W]

theorem isLat_comap (f : W →ₗ[LaurentSeries k] V) (hf : Function.Injective f)
    {N : Submodule (PowerSeries k) V} (hN : IsLat N) :
    IsLat (N.comap (f.restrictScalars (PowerSeries k))) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (f.restrictScalars (PowerSeries k)) hf ?_
    haveI : IsNoetherian (PowerSeries k) N := isNoetherian_of_fg_of_noetherian N hN.1
    exact isNoetherian_submodule.1 this _ (Submodule.map_comap_le _ _)
  · refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨m, hm⟩ := exists_pow_smul_mem hN.2 (f w)
    have hmem : ((PowerSeries.X : PowerSeries k) ^ m) • w ∈ N.comap (f.restrictScalars (PowerSeries k)) := by
      rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.map_smul_of_tower]
      exact hm
    have hne : algebraMap (PowerSeries k) (LaurentSeries k) ((PowerSeries.X : PowerSeries k) ^ m) ≠ 0 := by
      rw [map_pow]
      refine pow_ne_zero _ ?_
      intro h
      have hX : (PowerSeries.X : PowerSeries k) ≠ 0 := PowerSeries.X_ne_zero
      exact hX (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k) (by rw [map_zero]; exact h))
    rw [← Submodule.smul_mem_iff _ hne, algebraMap_smul]
    exact Submodule.subset_span hmem

end

theorem main : ∀ {k : Type} [inst : Field k] {V : Type} [inst_1 : AddCommGroup V]
    [inst_2 : Module (LaurentSeries k) V] [inst_3 : Module (PowerSeries k) V]
    [inst_4 : IsScalarTower (PowerSeries k) (LaurentSeries k) V] {W : Type} [inst_5 : AddCommGroup W]
    [inst_6 : Module (LaurentSeries k) W] [inst_7 : Module (PowerSeries k) W]
    [inst_8 : IsScalarTower (PowerSeries k) (LaurentSeries k) W] (f : LinearMap (RingHom.id (LaurentSeries k)) W V),
    Function.Injective (DFunLike.coe f) → ∀ {N : Submodule (PowerSeries k) V}, GlobalTheory.PhiGam.IsLat N →
      GlobalTheory.PhiGam.IsLat (Submodule.comap (LinearMap.restrictScalars (PowerSeries k) f) N) :=
  fun f hf _ hN => isLat_comap f hf hN

end GlobalTheory.LatticeComap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfNotDvd
section
open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem isUnit_of_not_dvd {ϖ b : O} (hϖ : Irreducible ϖ) (h : ¬ ϖ ∣ b) : IsUnit b := by
  by_contra hb
  have hm : b ∈ IsLocalRing.maximalIdeal O := hb
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.mem_span_singleton] at hm
  exact h hm

theorem alg_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : algebraMap O K ϖ ≠ 0 := by
  intro h
  exact hϖ.ne_zero (IsFractionRing.injective O K (by simpa using h))

theorem exists_unit_conj (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : Oˣ, cK (algebraMap O K ϖ) = algebraMap O K u * algebraMap O K ϖ := by
  have h1 : Irreducible (c ϖ) := (MulEquiv.irreducible_iff c.toMulEquiv).2 hϖ
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible O h1 hϖ
  refine ⟨u⁻¹, ?_⟩
  have e : c ϖ = ((u⁻¹ : Oˣ) : O) * ϖ := by
    calc c ϖ = c ϖ * u * ((u⁻¹ : Oˣ) : O) := by simp [mul_assoc]
      _ = ϖ * ((u⁻¹ : Oˣ) : O) := by rw [hu]
      _ = _ := mul_comm _ _
  rw [hcK, e, map_mul]

theorem exists_ratio {ϖ : O} (hϖ : Irreducible ϖ) {β γ : K}
    (hβ : β ∉ (algebraMap O K).range) (hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range)
    (hγ : algebraMap O K ϖ * γ ∈ (algebraMap O K).range) :
    ∃ a : O, γ = algebraMap O K a * β := by
  obtain ⟨b, hb⟩ := hβ'
  obtain ⟨g, hg⟩ := hγ
  have h0 : algebraMap O K ϖ ≠ 0 := alg_ne_zero hϖ
  have hbu : IsUnit b := by
    apply isUnit_of_not_dvd hϖ
    rintro ⟨e, rfl⟩
    apply hβ
    refine ⟨e, ?_⟩
    rw [map_mul] at hb
    exact (mul_left_cancel₀ h0 hb)
  obtain ⟨u, rfl⟩ := hbu
  refine ⟨g * ((u⁻¹ : Oˣ) : O), ?_⟩
  apply mul_left_cancel₀ h0
  have e1 : algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul]; simp
  rw [← hg, map_mul]
  calc algebraMap O K g = algebraMap O K g * (algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O)) := by
        rw [e1, mul_one]
    _ = algebraMap O K g * ((algebraMap O K ϖ * β) * algebraMap O K ((u⁻¹ : Oˣ) : O)) := by rw [hb]
    _ = _ := by ring

theorem ratio_mem_iff {ϖ : O} (hϖ : Irreducible ϖ) {β : K}
    (hβ : β ∉ (algebraMap O K).range) (hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range)
    (a : O) : algebraMap O K a * β ∈ (algebraMap O K).range ↔ ϖ ∣ a := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨u, rfl⟩ := isUnit_of_not_dvd hϖ hd
    apply hβ
    have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul]; simp
    have : β = algebraMap O K ((u⁻¹ : Oˣ) : O) * (algebraMap O K (u : O) * β) := by
      rw [← mul_assoc, e1, one_mul]
    rw [this]
    exact mul_mem ⟨_, rfl⟩ h
  · rintro ⟨e, rfl⟩
    rw [map_mul, mul_comm (algebraMap O K ϖ), mul_assoc]
    exact mul_mem ⟨_, rfl⟩ hβ'

theorem mul_pair_mem (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K} (hw : ϖ • v ∈ L)
    {l : Fin r → K} (hl : l ∈ L) :
    algebraMap O K ϖ * hf cK J v l ∈ (algebraMap O K).range := by
  obtain ⟨u, hu⟩ := exists_unit_conj c cK hcK (K := K) hϖ
  have h1 := (hSD _).1 hw l hl
  rw [hf_algSmul_left, hu] at h1
  have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
    rw [← map_mul]; simp
  have : algebraMap O K ϖ * hf cK J v l = algebraMap O K ((u⁻¹ : Oˣ) : O) *
      (algebraMap O K (u : O) * algebraMap O K ϖ * hf cK J v l) := by
    rw [mul_assoc, ← mul_assoc (algebraMap O K ((u⁻¹ : Oˣ) : O)), e1, one_mul]
  rw [this]
  exact mul_mem ⟨_, rfl⟩ h1

theorem perp_relIndex (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K} (hv : v ∉ L)
    (hw : ϖ • v ∈ L) :
    (perp cK J L v).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (IsLocalRing.ResidueField O) := by
  classical
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  set β := hf cK J v l0 with hβdef
  have hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hβ0 : β ≠ 0 := by
    intro h0
    exact hβ (h0 ▸ zero_mem _)
  have hex : ∀ l : L.toAddSubgroup, ∃ a : O, hf cK J v (l : Fin r → K) = algebraMap O K a * β :=
    fun l => exists_ratio hϖ hβ hβ' (mul_pair_mem c cK hcK hϖ hSD hw l.2)
  choose a ha using hex
  have hadd : ∀ x y : L.toAddSubgroup, a (x + y) = a x + a y := by
    intro x y
    apply IsFractionRing.injective O K
    apply mul_right_cancel₀ hβ0
    rw [← ha, map_add (f := _), add_mul, ← ha, ← ha]
    simpa using hf_add_right cK J v (x : Fin r → K) y
  let ψ : L.toAddSubgroup →+ IsLocalRing.ResidueField O :=
    AddMonoidHom.mk' (fun l => IsLocalRing.residue O (a l)) (by
      intro x y; rw [hadd, map_add (f := _)])
  have hker : (perp cK J L v).toAddSubgroup.addSubgroupOf L.toAddSubgroup = ψ.ker := by
    ext l
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change (l : Fin r → K) ∈ perp cK J L v ↔ IsLocalRing.residue O (a l) = 0
    rw [mem_perp, IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton,
      ← ratio_mem_iff hϖ hβ hβ', ← ha]
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
    have hm : b • l0 ∈ L.toAddSubgroup := L.smul_mem b hl0
    refine ⟨⟨b • l0, hm⟩, ?_⟩
    have : a ⟨b • l0, hm⟩ = b := by
      apply IsFractionRing.injective O K
      apply mul_right_cancel₀ hβ0
      rw [← ha]
      exact hf_algSmul_right cK J b v l0
    change IsLocalRing.residue O (a ⟨b • l0, hm⟩) = _
    rw [this]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj]
  exact Nat.card_congr AddSubgroup.topEquiv.toEquiv

theorem smul_injective {ϖ : O} (hϖ : Irreducible ϖ) :
    Function.Injective (fun x : Fin r → K => ϖ • x) := by
  intro x y h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  exact mul_left_cancel₀ (alg_ne_zero hϖ) this

theorem idx_eq_of_le {ϖ : O} (hϖ : Irreducible ϖ) {M L : Submodule O (Fin r → K)} (h : M ≤ L)
    (hi : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) : idx ϖ M = idx ϖ L := by
  set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'
  have hinj : Function.Injective f.toAddMonoidHom := smul_injective hϖ
  have e : ∀ P : Submodule O (Fin r → K),
      (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom := fun P => by
    ext x; simp [Submodule.mem_map]
  have hsub : ∀ P : Submodule O (Fin r → K), (P.map f).toAddSubgroup ≤ P.toAddSubgroup := by
    intro P x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact P.smul_mem ϖ hy
  have hBA : (M.map f).toAddSubgroup ≤ (L.map f).toAddSubgroup :=
    fun x hx => Submodule.map_mono h hx
  have hML : M.toAddSubgroup ≤ L.toAddSubgroup := h
  have e1 : (M.map f).toAddSubgroup.relIndex (L.map f).toAddSubgroup =
      M.toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  have h1 := AddSubgroup.relIndex_mul_relIndex _ _ _ hBA (hsub L)
  have h2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (hsub M) hML
  rw [e1] at h1
  have h3 : M.toAddSubgroup.relIndex L.toAddSubgroup * idx ϖ L =
      idx ϖ M * M.toAddSubgroup.relIndex L.toAddSubgroup := by
    simp only [idx]; rw [h1, h2]
  rw [mul_comm] at h3
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h3).symm

end GlobalTheory.HermNbr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitInvariantMapProper
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbitProper

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

theorem companionMatrixOfCoeffs_pow_mulVec_first_basis (p : Fin r → k) (n : ℕ) (hn : n < r) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) = Pi.single (⟨n, hn⟩ : Fin r) 1 := by
  induction n with
  | zero =>
    rw [pow_zero, one_mulVec]
    funext i
    simp [Pi.single_apply, Fin.ext_iff]
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih (by omega), mulVec_single_one]
    funext i
    simp only [companion, transpose_apply, of_apply, Pi.single_apply, Fin.ext_iff]
    have : ¬ (n + 1 = r) := by omega
    simp [this]

theorem conj_pow_GL (g : GL (Fin r) k) (A : Matrix (Fin r) (Fin r) k) (j : ℕ) :
    ((g : Matrix (Fin r) (Fin r) k) * A * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)) ^ j =
      (g : Matrix (Fin r) (Fin r) k) * A ^ j * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  exact Units.conj_pow g A j

theorem Bm_sec (a : Inv r k) : Bm (sec a) = 1 := by
  ext i j
  simp only [Bm, sec, of_apply]
  rw [companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2]
  simp [Pi.single_apply, Matrix.one_apply]

theorem Bm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by
  ext i j
  simp only [Bm, act, of_apply]
  rw [conj_pow_GL, mulVec_mulVec, mul_assoc _ _ (g : Matrix (Fin r) (Fin r) k), Units.inv_mul, mul_one,
    ← mulVec_mulVec]
  simp [Matrix.mul_apply, mulVec, dotProduct]

theorem Cm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  ext i j
  simp only [Cm, act, of_apply]
  rw [conj_pow_GL, vecMul_vecMul, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, ← vecMul_vecMul]
  simp [Matrix.mul_apply, vecMul, dotProduct]

theorem Cm_sec (a : Inv r k) : Cm (sec a) = hankel a := by
  ext i j
  simp only [Cm, hankel, mom, sec, of_apply]
  rw [pow_add, ← mulVec_mulVec, companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2, mulVec_single_one, dotProduct_comm]
  simp [vecMul, dotProduct, transpose_apply, mul_comm]

end Alg

section Top
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem cont_companion : Continuous (fun p : Fin r → F => companion p) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [companion, of_apply]
  split_ifs
  · exact ((continuous_apply i)).neg
  all_goals exact continuous_const

theorem cont_sec : Continuous (fun a : Inv r F => sec a) := by
  unfold sec
  exact (cont_companion.comp continuous_fst).prodMk
    (continuous_const.prodMk ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))

theorem cont_act : Continuous (fun p : GL (Fin r) F × Gl r F => act p.1 p.2) := by
  have h1 : Continuous (fun p : GL (Fin r) F × Gl r F => ((p.1 : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous (fun p : GL (Fin r) F × Gl r F => (((p.1)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
    Units.continuous_coe_inv.comp continuous_fst
  unfold act
  exact ((h1.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul h2).prodMk
    ((h1.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
      (((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_vecMul h2).prodMk
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))))

theorem cont_charpoly_coeff (i : ℕ) :
    Continuous (fun A : Matrix (Fin r) (Fin r) F => A.charpoly.coeff i) := by
  have h : ∀ A : Matrix (Fin r) (Fin r) F, A.charpoly.coeff i =
      MvPolynomial.eval (fun ij : Fin r × Fin r => A ij.1 ij.2)
        (MvPolynomial.map (Int.castRingHom F) ((Matrix.charpoly.univ ℤ (Fin r)).coeff i)) := by
    intro A
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  simp_rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem cont_mom (n : ℕ) : Continuous (fun Y : Gl r F => mom Y n) := by
  unfold mom
  exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).dotProduct
    (((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow n).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem cont_inv : Continuous (fun Y : Gl r F => inv Y) := by
  unfold inv
  exact (continuous_pi fun i : Fin r => (cont_charpoly_coeff (r := r) (F := F) (i : ℕ)).comp continuous_fst).prodMk
    ((continuous_pi fun i : Fin r => cont_mom (r := r) (F := F) (i : ℕ)).prodMk
      (show Continuous fun Y : Gl r F => Y.2.2.2 from continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem cont_hankel : Continuous (fun a : Inv r F => hankel a) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Inv r F => mom (sec a) ((i : ℕ) + (j : ℕ))
    exact (cont_mom _).comp cont_sec

theorem cont_Delta : Continuous (fun a : Inv r F => Delta a) := cont_hankel.matrix_det

end Top

section Cpt
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem cont_Bm : Continuous (fun Y : Gl r F => Bm Y) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun Y : Gl r F => ((Y.1 ^ (j : ℕ)) *ᵥ Y.2.1) i
    exact (continuous_apply i).comp
      (((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow _).matrix_mulVec
        (continuous_fst.comp continuous_snd))

theorem cont_Cm : Continuous (fun Y : Gl r F => Cm Y) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun Y : Gl r F => (Y.2.2.1 ᵥ* (Y.1 ^ (i : ℕ))) j
    exact (continuous_apply j).comp
      ((continuous_fst.comp (continuous_snd.comp continuous_snd)).matrix_vecMul
        ((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow _))

theorem contAt_hankel_inv (a : Inv r F) (ha : Delta a ≠ 0) :
    ContinuousAt (fun b : Inv r F => (hankel b)⁻¹) a := by
  refine (continuousAt_matrix_inv _ ?_).comp cont_hankel.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ha

theorem coe_eq (g : GL (Fin r) F) (a : Inv r F) :
    (g : Matrix (Fin r) (Fin r) F) = Bm (act g (sec a)) := by
  rw [Bm_act, Bm_sec, mul_one]

theorem coe_inv_eq (g : GL (Fin r) F) (a : Inv r F) (ha : Delta a ≠ 0) :
    ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = (hankel a)⁻¹ * Cm (act g (sec a)) := by
  have h : IsUnit (hankel a).det := isUnit_iff_ne_zero.mpr ha
  rw [Cm_act, Cm_sec, ← mul_assoc, nonsing_inv_mul _ h, one_mul]

theorem isCompact_set (C : Set (Gl r F)) (Ω : Set (Inv r F)) (hC : IsCompact C) (hΩ : IsCompact Ω)
    (hD : ∀ a ∈ Ω, Delta a ≠ 0) :
    IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  set Φ : Gl r F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    fun q => ((Bm q.1, MulOpposite.op ((hankel q.2)⁻¹ * Cm q.1)), q.2) with hΦdef
  have hΦ : ContinuousOn Φ (C ×ˢ Ω) := by
    intro q hq
    apply ContinuousAt.continuousWithinAt
    have h3 : ContinuousAt (fun q : Gl r F × Inv r F => (hankel q.2)⁻¹) q :=
      (contAt_hankel_inv q.2 (hD q.2 hq.2)).comp continuous_snd.continuousAt
    exact (((cont_Bm.comp continuous_fst).continuousAt).prodMk
      (MulOpposite.continuous_op.continuousAt.comp (h3.mul (cont_Cm.comp continuous_fst).continuousAt))).prodMk
      continuous_snd.continuousAt
  set e : GL (Fin r) F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    Prod.map (Units.embedProduct (Matrix (Fin r) (Fin r) F)) id with hedef
  have he : Topology.IsClosedEmbedding e :=
    Units.isClosedEmbedding_embedProduct.prodMap Topology.IsClosedEmbedding.id
  have hK : IsCompact (e ⁻¹' (Φ '' (C ×ˢ Ω))) :=
    he.isCompact_preimage ((hC.prod hΩ).image_of_continuousOn hΦ)
  have hS : IsClosed {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
    have hc : Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) :=
      cont_act.comp (continuous_fst.prodMk (cont_sec.comp continuous_snd))
    exact (hΩ.isClosed.preimage continuous_snd).inter (hC.isClosed.preimage hc)
  refine hK.of_isClosed_subset hS ?_
  rintro ⟨g, a⟩ ⟨ha, hY⟩
  refine ⟨(act g (sec a), a), ⟨hY, ha⟩, ?_⟩
  simp only [hΦdef, hedef, Prod.map, id, Units.embedProduct_apply]
  rw [← coe_eq g a, ← coe_inv_eq g a (hD a ha)]

end Cpt

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) ∧ Continuous (fun Y : Gl r F => inv Y) ∧ Continuous (fun a : Inv r F => Delta a) ∧ ∀ (C : Set (Gl r F)) (Ω : Set (Inv r F)), IsCompact C → IsCompact Ω → (∀ a ∈ Ω, Delta a ≠ 0) → IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  intro F E _ _ _ _ _ r
  exact ⟨cont_act.comp (continuous_fst.prodMk (cont_sec.comp continuous_snd)), cont_inv, cont_Delta,
    fun C Ω hC hΩ hD => isCompact_set C Ω hC hΩ hD⟩

end GlobalTheory.JR.OrbitProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

def IsUnrExt (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) : Prop :=
  K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧
    @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d

variable {K K' : UQ}

def overExt (φ : K.E →+* K'.E) (B : InvAlg K) (ψ : K'.E →+* B.A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) : InvAlg K' :=
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  haveI : IsScalarTower K'.O K'.E B.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite K'.E B.A := by
    obtain ⟨S, hS⟩ := B.fd.fg_top
    refine ⟨⟨S, eq_top_iff.2 fun y hy0 => ?_⟩⟩
    clear hy0
    have hy : y ∈ Submodule.span K.E (S : Set B.A) := hS ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      have h : e • x = (φ e) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hψ e]; rfl
      rw [h]; exact Submodule.smul_mem _ _ hx
  { A := B.A
    σ := B.σ
    σ_σ := B.σ_σ
    σ_alg := hσ
    g := B.g }

end GlobalTheory.UnitLemma.Unr
end
end

