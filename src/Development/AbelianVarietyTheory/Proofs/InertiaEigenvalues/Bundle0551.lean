module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModificationOfFiltration
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKModif

theorem mulFil {l : ℕ} [Fact l.Prime]
    (hmul : ∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b))
    (hanti : ∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a)
    {p q n : Type} [Fintype q] (M : Matrix p q (Per.BdR l)) (Q : Matrix q n (Per.BdR l))
    (a : p → q → ℤ) (b : q → n → ℤ) (c : p → n → ℤ)
    (hM : ∀ r t, M r t ∈ Per.FilD l (a r t)) (hQ : ∀ t j, Q t j ∈ Per.FilD l (b t j))
    (h : ∀ r t j, c r j ≤ a r t + b t j) (r : p) (j : n) : (M * Q) r j ∈ Per.FilD l (c r j) := by
  rw [Matrix.mul_apply]
  exact Submodule.sum_mem _ fun t _ => hanti _ _ (h r t j) (hmul _ _ _ _ (hM r t) (hQ t j))

theorem mul_comm_of_scalar {R : Type} [CommRing R] [IsDomain R] {d : ℕ} (X X' : Matrix (Fin d) (Fin d) R)
    (a : R) (ha : a ≠ 0) (h : X * X' = a • (1 : Matrix (Fin d) (Fin d) R)) :
    X' * X = a • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : X.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact pow_ne_zero _ ha this.symm
  have h1 : X * (X' * X - a • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      sub_self]
  have h2 : X.det • (X' * X - a • 1) = 0 := by
    have : X.det • (X' * X - a • 1) = (X.adjugate * X) * (X' * X - a • 1) := by
      rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [this, Matrix.mul_assoc, h1, Matrix.mul_zero]
  have h3 : X' * X - a • 1 = 0 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this
    simpa using (mul_eq_zero.1 this).resolve_left hdet
  exact sub_eq_zero.1 h3

theorem map_smul_ringHom {R S : Type} [CommRing R] [CommRing S] {p q : Type} (f : R →+* S) (a : R)
    (M : Matrix p q R) : (a • M).map f = f a • M.map f := by
  ext i j
  simp

theorem l_ne_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) : (l : bk.S) ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.constantCoeff) h
  simp only [map_natCast] at this
  have h1 := WittVector.coeff_p_one (p := l) (R := Fq l bk.a)
  rw [this] at h1
  simp at h1


set_option maxHeartbeats 1000000 in
theorem exists_modification_of_filtration : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (U U' : Matrix (Fin d) (Fin d) (Per.BdR l)), U * U' = 1 → ∀ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), (∀ i, |k i| ≤ N) → (∀ r s, U r s ∈ Per.FilD l (-(N : ℤ))) → (∀ r i, (U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) → (∀ i j, β i j ∈ Per.FilD l (-k i)) → U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 → ∃ (c₂ : ℕ) (X X' : Matrix (Fin d) (Fin d) (bk.S)), X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) ∧ (∀ i j, (U * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) ∧ (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') i j ∈ Per.FilD l N) := by
  intro l _ K bk C d U U' hUU' N m k c β hk hU hUc hβ hUcβ
  obtain ⟨hFilP, hmul, hanti, hP, -, hxi, -⟩ := _root_.GlobalTheory.MemLoc.seed_fil l C (bk.ev bk.E) bk.span_ev
  have hcc_apply : ∀ r i, c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) r i =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o ((c r i : ↥K.1) : Om l)) := fun r i => rfl
  generalize c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) = cc at hcc_apply hUc hUcβ ⊢
  have hφdef : ∀ x, ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) x =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev x)) := fun x => rfl
  generalize (algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev) = φ at hφdef ⊢
  have hmap0 : ∀ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l 0 := by
    intro z
    have := (hP 0 z).2 (by rw [hFilP 0, pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top)
    simpa using this
  have hφ0 : ∀ x : bk.S, φ x ∈ Per.FilD l 0 := fun x => by rw [hφdef]; exact hmap0 _
  have hone : (1 : Per.BdR l) ∈ Per.FilD l 0 := by simpa using hmap0 1
  have hepow : ∀ n : ℕ, φ bk.E ^ n ∈ Per.FilD l n := by
    intro n
    have : φ bk.E ^ n * 1 ∈ Per.FilD l (0 + n) := by rw [hφdef]; exact (hxi 0 n 1).2 hone
    simpa using this
  have hlu : IsUnit ((l : ℕ) : Per.BdRp l) := by
    have h := (GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))
    rwa [map_natCast] at h
  have hl0 := l_ne_zero bk

  have hlift := fun r i => GlobalTheory.T.exists_breuilKisin_lift_compatible_bdR_prisms l K bk C (2 * N) (c r i)
  choose k0 s0 hs0 hnp0 using hlift
  obtain ⟨κ, hkκ⟩ : ∃ κ : ℕ, ∀ r i, k0 r i ≤ κ := ⟨Finset.univ.sup (fun p : Fin d × Fin m => k0 p.1 p.2),
    fun r i => Finset.le_sup (f := fun p : Fin d × Fin m => k0 p.1 p.2) (Finset.mem_univ (r, i))⟩
  have hlκ0 : (l : Per.BdR l) ^ κ ∈ Per.FilD l 0 := by simpa using hmap0 (((l : ℕ) : Per.BdRp l) ^ κ)
  obtain ⟨s, hs⟩ : ∃ s : Matrix (Fin d) (Fin m) bk.S, ∀ r i, s r i = (l : bk.S) ^ (κ - k0 r i) * s0 r i :=
    ⟨fun r i => (l : bk.S) ^ (κ - k0 r i) * s0 r i, fun _ _ => rfl⟩
  have hnp : ∀ r i, ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ,
      BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (BK.hf f (s r i) - BK.hf g (s r i)) := by
    intro r i B f g
    obtain ⟨k', hk'⟩ := hnp0 r i B f g
    refine ⟨k', ?_⟩
    have : (l : B.A) ^ k' * (BK.hf f (s r i) - BK.hf g (s r i)) =
        (l : B.A) ^ (κ - k0 r i) * ((l : B.A) ^ k' * (BK.hf f (s0 r i) - BK.hf g (s0 r i))) := by
      simp only [hs, map_mul, map_pow, map_natCast]; ring
    rw [this]
    exact Dvd.dvd.mul_left hk' _
  have hF : ∀ r i, (s.map φ - (l : Per.BdR l) ^ κ • cc) r i ∈ Per.FilD l ((2 * N : ℕ) : ℤ) := by
    intro r i
    have hmem : ((l : ℕ) : Per.BdRp l) ^ (κ - k0 r i) * (aDp l (bk.ev (s0 r i)) -
        ((l : ℕ) : Per.BdRp l) ^ k0 r i * C.o ((c r i : ↥K.1) : Om l)) ∈ Per.FilP l (2 * N) :=
      Ideal.mul_mem_left _ _ (hs0 r i)
    have h2 := (hP (2 * N) _).2 hmem
    convert h2 using 1
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, hcc_apply, smul_eq_mul]
    simp only [hφdef, hs, map_mul, map_pow, map_natCast, map_sub]
    rw [← pow_sub_mul_pow (l : Per.BdR l) (hkκ r i)]
    ring
  have hFt : ∀ t i, (s.map φ - (l : Per.BdR l) ^ κ • cc) t i ∈ Per.FilD l (2 * (N : ℤ)) := by
    intro t i; have := hF t i; push_cast at this; exact this
  obtain ⟨n, hn⟩ : ∃ n : Fin m → ℕ, ∀ i, (n i : ℤ) = N - k i := ⟨fun i => ((N : ℤ) - k i).toNat, fun i =>
    Int.toNat_of_nonneg (by have := (abs_le.1 (hk i)).2; linarith)⟩
  obtain ⟨c₂, X, X', R, Q, Q', hXX', hX, hY⟩ :=
    _root_.GlobalTheory.BSP.LocalizedLatticeBasis.exists_lattice_basis l K bk d m (2 * N) (s * Matrix.diagonal fun i => bk.E ^ n i)
  refine ⟨c₂, X, X', hXX', _root_.GlobalTheory.seed_nopole l K bk d m N c₂ s n X X' R Q Q' hnp hXX' hX hY, ?_, ?_⟩
  ·
    have hXφ : X.map φ = (s.map φ * Matrix.diagonal (fun i => φ bk.E ^ n i)) * Q.map φ +
        φ bk.E ^ (2 * N) • R.map φ := by
      rw [hX, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero φ), map_smul_ringHom]
      simp only [map_pow]
    have hUs : ∀ r i, (U * s.map φ) r i = (l : Per.BdR l) ^ κ * (U * cc) r i +
        (U * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i := by
      intro r i
      simp [Matrix.mul_sub, Matrix.mul_smul]
    have hUs_mem : ∀ r i, ((U * s.map φ) * Matrix.diagonal (fun i => φ bk.E ^ n i)) r i ∈ Per.FilD l N := by
      intro r i
      rw [Matrix.mul_diagonal, hUs, add_mul]
      refine add_mem ?_ ?_
      · have h1 : (l : Per.BdR l) ^ κ * (U * cc) r i ∈ Per.FilD l (0 + k i) := hmul _ _ _ _ hlκ0 (hUc r i)
        have := hmul _ _ _ _ h1 (hepow (n i))
        rwa [hn i, show (0 + k i + (N - k i) : ℤ) = N by ring] at this
      · have h1 : (U * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i ∈ Per.FilD l N :=
          mulFil hmul hanti U _ (fun _ _ => -(N : ℤ)) (fun _ _ => 2 * (N : ℤ)) (fun _ _ => (N : ℤ)) hU hFt
            (fun _ _ _ => by linarith) r i
        have := hmul _ _ _ _ h1 (hepow (n i))
        exact hanti _ _ (by have := hn i; have := (abs_le.1 (hk i)).2; linarith) this
    intro r j
    rw [hXφ, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine add_mem ?_ ?_
    · exact mulFil hmul hanti _ _ (fun _ _ => (N : ℤ)) (fun _ _ => 0) (fun _ _ => (N : ℤ)) hUs_mem
        (fun t j => hφ0 _) (fun _ _ _ => by simp) r j
    · have h1 := mulFil hmul hanti U (R.map φ) (fun _ _ => -(N : ℤ)) (fun _ _ => 0) (fun _ _ => -(N : ℤ)) hU
        (fun t j => hφ0 _) (fun _ _ _ => by simp) r j
      have := hmul _ _ _ _ (hepow (2 * N)) h1
      exact hanti _ _ (by push_cast; linarith) this
  ·
    have ha : ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ bk.E_ne_zero)
    have hX'X := mul_comm_of_scalar X X' _ ha hXX'
    have hS : X' * (s * Matrix.diagonal fun i => bk.E ^ n i) = bk.E ^ (2 * N) • Q' := by
      have h1 : (l : bk.S) ^ c₂ • (X' * (s * Matrix.diagonal fun i => bk.E ^ n i)) =
          (l : bk.S) ^ c₂ • (bk.E ^ (2 * N) • Q') := by
        rw [← Matrix.mul_smul, hY, ← Matrix.mul_assoc, hX'X, Matrix.smul_mul, Matrix.one_mul, smul_smul]
      refine Matrix.ext fun r i => ?_
      have := congrFun (congrFun h1 r) i
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ (pow_ne_zero _ hl0) this
    have hcol : ∀ r i, (X'.map φ * s.map φ) r i * φ bk.E ^ n i = φ bk.E ^ (2 * N) * φ (Q' r i) := by
      intro r i
      have := congrArg φ (congrFun (congrFun hS r) i)
      rw [← Matrix.mul_assoc, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, map_pow,
        map_pow] at this
      rw [← Matrix.map_mul]
      exact this
    have hXs : ∀ r i, (X'.map φ * s.map φ) r i ∈ Per.FilD l (N + k i) := by
      intro r i
      refine (hxi (N + k i) (n i) _).1 ?_
      rw [← hφdef]
      rw [mul_comm, hcol, hn i, show ((N : ℤ) + k i + (N - k i) : ℤ) = 2 * (N : ℤ) + 0 by ring]
      have := hmul _ _ _ _ (hepow (2 * N)) (hφ0 (Q' r i))
      push_cast at this
      exact this
    have hXc : ∀ r i, (l : Per.BdR l) ^ κ * (X'.map φ * cc) r i ∈ Per.FilD l (N + k i) := by
      intro r i
      have hsplit : (l : Per.BdR l) ^ κ * (X'.map φ * cc) r i = (X'.map φ * s.map φ) r i -
          (X'.map φ * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i := by
        simp [Matrix.mul_sub, Matrix.mul_smul]
      rw [hsplit]
      refine sub_mem (hXs r i) ?_
      exact mulFil hmul hanti _ _ (fun _ _ => 0) (fun _ _ => 2 * (N : ℤ)) (fun _ i => (N : ℤ) + k i)
        (fun _ _ => hφ0 _) hFt (fun _ _ i => by have := (abs_le.1 (hk i)).2; linarith) r i
    intro r j
    have hU'eq : U' = cc * β := by
      have h1 : U' * U = 1 := mul_eq_one_comm.1 hUU'
      calc U' = U' * (U * cc * β) := by rw [hUcβ, Matrix.mul_one]
        _ = (U' * U) * cc * β := by simp only [Matrix.mul_assoc]
        _ = cc * β := by rw [h1, Matrix.one_mul]
    have hfin : (l : Per.BdR l) ^ κ * (X'.map φ * U') r j ∈ Per.FilD l N := by
      rw [hU'eq, ← Matrix.mul_assoc, Matrix.mul_apply, Finset.mul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← mul_assoc]
      have := hmul _ _ _ _ (hXc r i) (hβ i j)
      rwa [show (N : ℤ) + k i + -k i = N by ring] at this
    obtain ⟨u, hu⟩ := hlu
    have hinv : ((↑(u⁻¹ ^ κ) : Per.BdRp l)) * ((l : ℕ) : Per.BdRp l) ^ κ = 1 := by
      rw [← hu, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    have key := Submodule.smul_mem _ ((↑(u⁻¹ ^ κ) : Per.BdRp l)) hfin
    rw [Algebra.smul_def, ← mul_assoc,
      show (l : Per.BdR l) ^ κ = algebraMap (Per.BdRp l) (Per.BdR l) (((l : ℕ) : Per.BdRp l) ^ κ) by simp,
      ← map_mul, hinv, map_one, one_mul] at key
    exact key

end GlobalTheory.BKModif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableComplActK
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

namespace GlobalTheory.BlockSum

section General

variable {K : Type} [Field K] {Γ : Type}

def StableUnder {V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V)
    (S : Submodule K V) : Prop :=
  ∀ γ, ∀ v ∈ S, f γ v ∈ S

def HasRelCompl {V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V)
    (Y : Submodule K V) : Prop :=
  ∀ W : Submodule K V, StableUnder f W → W ≤ Y →
    ∃ C : Submodule K V, StableUnder f C ∧ C ≤ Y ∧ W ⊓ C = ⊥ ∧ W ⊔ C = Y

variable {V : Type} [AddCommGroup V] [Module K V] {f : Γ → V →ₗ[K] V}

theorem hasRelCompl_sup {X U : Submodule K V} (hXs : StableUnder f X) (hUs : StableUnder f U)
    (hX : HasRelCompl f X) (hU : HasRelCompl f U) : HasRelCompl f (X ⊔ U) := by
  first
  | exact @_root_.GlobalTheory.ComplementedSup.complemented_sup
  | exact _root_.GlobalTheory.ComplementedSup.complemented_sup
  | (apply _root_.GlobalTheory.ComplementedSup.complemented_sup <;> assumption)
  | (intros; apply _root_.GlobalTheory.ComplementedSup.complemented_sup <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ComplementedSup.complemented_sup <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ComplementedSup.complemented_sup ..)

end General

section Blocks

variable {K : Type} [Field K] {Γ : Type} {ι : Type} [DecidableEq ι]
  {n : Type} [Fintype n] [DecidableEq n]

def blockAct (ρ : Γ → ι → Matrix n n K) (γ : Γ) : (ι → n → K) →ₗ[K] (ι → n → K) :=
  LinearMap.pi (fun b => (Matrix.mulVecLin (ρ γ b)).comp (LinearMap.proj b))

theorem blockAct_apply (ρ : Γ → ι → Matrix n n K) (γ : Γ) (v : ι → n → K) (b : ι) :
    blockAct ρ γ v b = (ρ γ b).mulVec (v b) := rfl

def blockSub (s : Set ι) : Submodule K (ι → n → K) where
  carrier := {v | ∀ b, b ∉ s → v b = 0}
  add_mem' := by
    intro v w hv hw b hb
    simp [hv b hb, hw b hb]
  zero_mem' := by
    intro b _
    rfl
  smul_mem' := by
    intro c v hv b hb
    simp [hv b hb]

theorem blockSub_stable (ρ : Γ → ι → Matrix n n K) (s : Set ι) :
    StableUnder (blockAct ρ) (blockSub s : Submodule K (ι → n → K)) := by
  intro γ v hv b hb
  rw [blockAct_apply, hv b hb, Matrix.mulVec_zero]

theorem blockSub_mono {s t : Set ι} (h : s ⊆ t) :
    (blockSub s : Submodule K (ι → n → K)) ≤ blockSub t :=
  fun _ hv b hb => hv b (fun hs => hb (h hs))

theorem blockSub_empty : (blockSub (∅ : Set ι) : Submodule K (ι → n → K)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  funext b
  exact hv b (Set.notMem_empty b)

theorem blockSub_univ : (blockSub (Set.univ : Set ι) : Submodule K (ι → n → K)) = ⊤ := by
  rw [eq_top_iff]
  intro v _ b hb
  exact absurd (Set.mem_univ b) hb

theorem blockSub_insert (b : ι) (s : Set ι) :
    (blockSub (insert b s) : Submodule K (ι → n → K)) = blockSub s ⊔ blockSub {b} := by
  apply le_antisymm
  · intro v hv
    refine Submodule.mem_sup.mpr ⟨Function.update v b 0, ?_, Pi.single b (v b), ?_, ?_⟩
    · intro c hc
      by_cases h : c = b
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact hv c (by simp [h, hc])
    · intro c hc
      have h : c ≠ b := by simpa using hc
      simp [h]
    · funext c
      by_cases h : c = b
      · subst h; simp
      · simp [h]
  · exact sup_le (blockSub_mono (Set.subset_insert _ _))
      (blockSub_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))

def BlockHasCompl (ρ : Γ → ι → Matrix n n K) (b : ι) : Prop :=
  ∀ S : Submodule K (n → K), (∀ γ, ∀ y ∈ S, (ρ γ b).mulVec y ∈ S) →
    ∃ D : Submodule K (n → K), (∀ γ, ∀ y ∈ D, (ρ γ b).mulVec y ∈ D) ∧ IsCompl S D

theorem hasRelCompl_single (ρ : Γ → ι → Matrix n n K) (b : ι) (hb : BlockHasCompl ρ b) :
    HasRelCompl (blockAct ρ) (blockSub ({b} : Set ι) : Submodule K (ι → n → K)) := by
  intro W hW hWY
  obtain ⟨D', hD's, hc⟩ := hb (W.map (LinearMap.proj b)) (by
    rintro γ _ ⟨v, hv, rfl⟩
    exact ⟨blockAct ρ γ v, hW γ v hv, rfl⟩)
  have hDle : D'.map (LinearMap.single K (fun _ : ι => n → K) b) ≤ blockSub {b} := by
    rintro _ ⟨y, _, rfl⟩ c hc
    have h : c ≠ b := by simpa using hc
    simp [h]
  refine ⟨D'.map (LinearMap.single K (fun _ : ι => n → K) b), ?_, hDle, ?_, ?_⟩
  · rintro γ _ ⟨y, hy, rfl⟩
    refine ⟨(ρ γ b).mulVec y, hD's γ y hy, ?_⟩
    funext c
    rw [blockAct_apply]
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  · rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hvD⟩ := Submodule.mem_inf.mp hv
    obtain ⟨y, hy, rfl⟩ := hvD
    have hy0 : y = 0 := by
      have hm : y ∈ W.map (LinearMap.proj b) ⊓ D' :=
        Submodule.mem_inf.mpr ⟨⟨_, hvW, by simp⟩, hy⟩
      rw [hc.inf_eq_bot] at hm
      exact (Submodule.mem_bot K).mp hm
    subst hy0
    simp
  · apply le_antisymm (sup_le hWY hDle)
    intro u hu
    have hub : u b ∈ W.map (LinearMap.proj b) ⊔ D' := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨s', ⟨v, hv, rfl⟩, d', hd', hsum⟩ := Submodule.mem_sup.mp hub
    refine Submodule.mem_sup.mpr ⟨v, hv, Pi.single b d', ⟨d', hd', by simp⟩, ?_⟩
    funext c
    by_cases h : c = b
    · subst h
      simpa using hsum
    · have h1 : u c = 0 := hu c (by simpa using h)
      have h2 : v c = 0 := hWY hv c (by simpa using h)
      simp [h, h1, h2]

theorem hasRelCompl_finset (ρ : Γ → ι → Matrix n n K) (hblk : ∀ b, BlockHasCompl ρ b)
    (s : Finset ι) :
    HasRelCompl (blockAct ρ) (blockSub (s : Set ι) : Submodule K (ι → n → K)) := by
  refine Finset.induction_on s ?_ ?_
  · intro W _ hWY
    rw [Finset.coe_empty, blockSub_empty] at hWY ⊢
    refine ⟨⊥, fun γ v hv => ?_, le_rfl, inf_bot_eq _, ?_⟩
    · rw [(Submodule.mem_bot K).mp hv, map_zero]; exact Submodule.zero_mem _
    · rw [sup_bot_eq]; exact le_antisymm hWY bot_le
  · intro b s _ ih
    rw [Finset.coe_insert, blockSub_insert]
    exact hasRelCompl_sup (blockSub_stable ρ _) (blockSub_stable ρ _) ih
      (hasRelCompl_single ρ b (hblk b))

theorem exists_stable_compl [Fintype ι] (ρ : Γ → ι → Matrix n n K)
    (hblk : ∀ b, BlockHasCompl ρ b) (W : Submodule K (ι → n → K))
    (hW : StableUnder (blockAct ρ) W) :
    ∃ C : Submodule K (ι → n → K), StableUnder (blockAct ρ) C ∧ IsCompl W C := by
  have h := hasRelCompl_finset ρ hblk Finset.univ W hW
    (by rw [Finset.coe_univ, blockSub_univ]; exact le_top)
  rw [Finset.coe_univ, blockSub_univ] at h
  obtain ⟨C, hCs, _, h1, h2⟩ := h
  exact ⟨C, hCs, ⟨disjoint_iff.mpr h1, codisjoint_iff.mpr h2⟩⟩

end Blocks

end GlobalTheory.BlockSum

namespace GlobalTheory.BlockSum


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_stable_compl_actK : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)), GoodR D.nd i r → ∀ {a : ℕ} (x : Fin a → ↥Xs)
    (W : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i)),
    (∀ γ : GE D.nd, ∀ v ∈ W, actK i r Xs x γ v ∈ W) →
    ∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧ IsCompl W C := by
  intro D i r Xs hG a x W hW
  let ρ : GE D.nd → Fin a → Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i) :=
    fun γ b => (mapM (toK D.nd i) (rTwO D.nd i r ↑(x b))) γ
  have hact : ∀ γ v, actK i r Xs x γ v = blockAct ρ γ v := fun γ v => rfl
  have hblk : ∀ b, BlockHasCompl ρ b := by
    intro b
    have hss := (hG ↑(x b)).2.1
    set c : GE D.nd → KK D.nd i :=
      fun γ => toK D.nd i ((((chiU D.nd i 1)⁻¹ γ : (D.nd.O i)ˣ)) : D.nd.O i) with hcdef
    have hrel : ∀ γ, ρ γ b = c γ • (↑(mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r ↑(x b)) γ) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
      intro γ
      ext j k
      simp [ρ, c, mapM, rTwO, twistM, mapRep, rO]
    have hc0 : ∀ γ, c γ ≠ 0 := fun γ =>
      ((((chiU D.nd i 1)⁻¹ γ : (D.nd.O i)ˣ)).isUnit.map (toK D.nd i)).ne_zero
    intro S hS
    obtain ⟨D', hD', hcompl⟩ := hss S (by
      intro g y hy
      have h := hS g y hy
      rw [hrel, Matrix.smul_mulVec] at h
      have h2 := S.smul_mem (c g)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ (hc0 g), one_smul] at h2)
    refine ⟨D', fun g y hy => ?_, hcompl⟩
    rw [hrel, Matrix.smul_mulVec]
    exact D'.smul_mem _ (hD' g y hy)
  obtain ⟨C, hCs, hc⟩ := exists_stable_compl ρ hblk W (fun γ v hv => by
    rw [← hact]; exact hW γ v hv)
  exact ⟨C, fun γ v hv => by rw [hact]; exact hCs γ v hv, hc⟩

end GlobalTheory.BlockSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWachImageIsClosedStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weakTopology_wachImage_isClosed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T))) := by
  first | exact @GlobalTheory.WeakClosedX.jD_XN_closed | exact GlobalTheory.WeakClosedX.jD_XN_closed | (intros; apply GlobalTheory.WeakClosedX.jD_XN_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWildInertiaGeneratingCyclotomicValueStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wildInertia_generating_cyclotomicValue : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∃ g0 : GE D.nd, (∃ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) ∧ (∃ u : ℤ_[D.nd.l i]ˣ, ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) = 1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → g0 ∈ wildSet D.nd (D.nd.plOm.1 w) := by
  first | exact @GlobalTheory.WildCycGen.main | exact GlobalTheory.WildCycGen.main | (intros; apply GlobalTheory.WildCycGen.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittPowerSeriesApproxMatrixBdRPlusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wittPowerSeries_approx_matrix_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (c : Matrix (Fin d) (Fin d) (Om l)), (∀ i j, c i j ∈ K.1) → ∀ n : ℕ, ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * C.o (c i j) ∈ Per.FilP l n := by
  first | (exact @GlobalTheory.LiftMatK.lift_matrix) | (exact GlobalTheory.LiftMatK.lift_matrix) | (intros; apply GlobalTheory.LiftMatK.lift_matrix  <;> assumption)
end

