module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0171
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeAdaptedBasis
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.GoodLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem sigR_inclR (A : Type) [CommRing A] [Algebra F A] (e : E) :
    sigR A σ (inclR (F := F) A e) = inclR (F := F) A (σ e) := by
  simp [sigR, inclR]

theorem dual_mulVec (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (z : Fin n → Fv F v ⊗[F] E) (i : Fin r) :
    ((cT (σ : E →+* E) A * J).map (inclR (F := F) (Fv F v)) *ᵥ z) i
      = hR (Fv F v) σ J (colV v A i) z := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, colV, JR, sigR_inclR, mulVec, dotProduct, map_apply, Matrix.mul_apply,
    cT, transpose_apply, map_sum, map_mul, Finset.sum_mul, RingHom.coe_coe]
  rw [Finset.sum_comm]

theorem col_mulVec (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (w : Fin r → Fv F v ⊗[F] E) :
    A.map (inclR (F := F) (Fv F v)) *ᵥ w = ∑ i, w i • colV v A i := by
  ext a
  simp [mulVec, dotProduct, colV, Finset.sum_apply, mul_comm]

theorem hR_colV (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin n) (Fin r) E) (i j : Fin r) :
    hR (Fv F v) σ J (colV v A i) (colV v B j)
      = inclR (F := F) (Fv F v) ((cT (σ : E →+* E) A * J * B) i j) := by
  rw [← dual_mulVec]
  conv_rhs => rw [Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_apply, colV, map_sum, map_mul]

theorem sigma_sigma (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]

theorem cT_mul_rect (s : E →+* E) {a b c : Type} [Fintype b] (P : Matrix a b E) (Q : Matrix b c E) :
    cT s (P * Q) = cT s Q * cT s P := by
  simp [cT, Matrix.map_mul, transpose_mul]

theorem gram_yx (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) : cT (σ : E →+* E) Y * J * X = 1 := by
  have hcT : cT (σ : E →+* E) J = J := by
    ext i j
    exact hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j
    exact sigma_sigma hCM _
  have h1 : cT (σ : E →+* E) (1 : Matrix (Fin r) (Fin r) E) = 1 := by
    ext i j
    simp [cT, Matrix.one_apply, eq_comm]
  have := congrArg (cT (σ : E →+* E)) hW.xy
  rw [cT_mul_rect, cT_mul_rect, hcT, hcc, h1, ← Matrix.mul_assoc] at this
  exact this

def projP (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (X Y : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  1 - X.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) Y * J).map (inclR (F := F) (Fv F v))
    - Y.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) X * J).map (inclR (F := F) (Fv F v))

theorem projP_mulVec (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin r) E)
    (z : Fin n → Fv F v ⊗[F] E) :
    projP v σ J X Y *ᵥ z = z - ∑ i, hR (Fv F v) σ J (colV v Y i) z • colV v X i
      - ∑ i, hR (Fv F v) σ J (colV v X i) z • colV v Y i := by
  have hb : ∀ A B : Matrix (Fin n) (Fin r) E,
      (A.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) B * J).map (inclR (F := F) (Fv F v))) *ᵥ z
        = ∑ i, hR (Fv F v) σ J (colV v B i) z • colV v A i := by
    intro A B
    rw [← mulVec_mulVec, col_mulVec]
    simp only [dual_mulVec]
  simp only [projP, sub_mulVec, one_mulVec, hb]

theorem leviMat_mulVec (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin r) E)
    (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (z : Fin n → Fv F v ⊗[F] E) :
    leviMat σ J (Fv F v) X Y M *ᵥ z =
      ∑ i, (hR (Fv F v) σ J (colV v Y i) (M *ᵥ colV v X i) * hR (Fv F v) σ J (colV v Y i) z) • colV v X i
      + ∑ i, (hR (Fv F v) σ J (colV v X i) (M *ᵥ colV v Y i) * hR (Fv F v) σ J (colV v X i) z) • colV v Y i
      + projP v σ J X Y *ᵥ (M *ᵥ (projP v σ J X Y *ᵥ z)) := by
  have hd : ∀ (A B : Matrix (Fin n) (Fin r) E) (i : Fin r),
      ((cT (σ : E →+* E) A * J).map (inclR (F := F) (Fv F v)) * M * B.map (inclR (F := F) (Fv F v))) i i
        = hR (Fv F v) σ J (colV v A i) (M *ᵥ colV v B i) := by
    intro A B i
    rw [← dual_mulVec, Matrix.mul_assoc]
    rfl
  have hmv : ∀ (A B : Matrix (Fin n) (Fin r) E) (d : Fin r → Fv F v ⊗[F] E),
      (A.map (inclR (F := F) (Fv F v)) * diagonal d * (cT (σ : E →+* E) B * J).map (inclR (F := F) (Fv F v))) *ᵥ z
        = ∑ i, (d i * hR (Fv F v) σ J (colV v B i) z) • colV v A i := by
    intro A B d
    rw [← mulVec_mulVec, ← mulVec_mulVec, col_mulVec]
    simp only [mulVec_diagonal, dual_mulVec]
  unfold leviMat
  simp only [add_mulVec]
  rw [hmv, hmv]
  simp only [hd]
  simp only [mulVec_mulVec, projP, Matrix.mul_assoc]

theorem hR_isom {v : HeightOneSpectrum (𝓞 F)} (g : GLoc σ J v) (a b : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J ((matHom _ σ J g).1 *ᵥ a) ((matHom _ σ J g).1 *ᵥ b) = hR (Fv F v) σ J a b := by
  have hg : cT (sigR (Fv F v) σ) (matHom _ σ J g).1 * JR (Fv F v) J * (matHom _ σ J g).1 = JR (Fv F v) J := g.2
  simp only [hR]
  rw [Formalism.UG.P.hform_mulVec, hg]

theorem levi_mem_stabLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ → ∀ (p m : GLoc σ J v), p ∈ stabLat σ J Λ → ∀ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id → (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B → (matHom _ σ J m).1 = leviMat σ J (Fv F v) X Y (matHom _ σ J p).1 → m ∈ stabLat σ J Λ := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW v Λ hΛ hA p m hp B _ _ hm
  obtain ⟨-, ⟨hint, heven⟩, hmax⟩ := hΛ
  have hxx : ∀ i j, hR (Fv F v) σ J (colV v X i) (colV v X j) = 0 := fun i j => by
    rw [hR_colV, hW.xx]; simp
  have hyy : ∀ i j, hR (Fv F v) σ J (colV v Y i) (colV v Y j) = 0 := fun i j => by
    rw [hR_colV, hW.yy]; simp
  have hxy : ∀ i j, hR (Fv F v) σ J (colV v X i) (colV v Y j) = if i = j then 1 else 0 := fun i j => by
    rw [hR_colV, hW.xy, Matrix.one_apply]; split_ifs <;> simp
  have hyx : ∀ i j, hR (Fv F v) σ J (colV v Y i) (colV v X j) = if i = j then 1 else 0 := fun i j => by
    rw [hR_colV, gram_yx hCM hJ hW, Matrix.one_apply]; split_ifs <;> simp
  have hδ : ∀ i j : Fin r, ((if i = j then 1 else 0 : Fv F v ⊗[F] E)) ∈ intLoc F E v := fun i j => by
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hx : ∀ i, colV v X i ∈ Λ := fun i => by
    refine (hA _).2 ⟨fun j => ?_, fun j => ?_, ?_⟩
    · rw [hxx]; exact zero_mem _
    · rw [hyx]; exact hδ _ _
    · simp [hxx, hyx]
  have hy : ∀ i, colV v Y i ∈ Λ := fun i => by
    refine (hA _).2 ⟨fun j => ?_, fun j => ?_, ?_⟩
    · rw [hxy]; exact hδ _ _
    · rw [hyy]; exact zero_mem _
    · simp [hxy, hyy]
  have hP : ∀ z ∈ Λ, projP v σ J X Y *ᵥ z ∈ Λ := fun z hz => by
    rw [projP_mulVec]
    exact ((hA z).1 hz).2.2
  have hsm : ∀ a ∈ intLoc F E v, ∀ z ∈ Λ, a • z ∈ Λ := fun a ha z hz => Λ.smul_mem ⟨a, ha⟩ hz
  have hpz : ∀ z ∈ Λ, (matHom _ σ J p).1 *ᵥ z ∈ Λ := fun z hz => (hp z).1 hz
  have hsub : ∀ z ∈ Λ, (matHom _ σ J m).1 *ᵥ z ∈ Λ := fun z hz => by
    rw [hm, leviMat_mulVec]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) (sum_mem fun i _ => ?_)) (hP _ (hpz _ (hP z hz)))
    · exact hsm _ (mul_mem (hint _ (hy i) _ (hpz _ (hx i))) (hint _ (hy i) _ hz)) _ (hx i)
    · exact hsm _ (mul_mem (hint _ (hx i) _ (hpz _ (hy i))) (hint _ (hx i) _ hz)) _ (hy i)
  let L' : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := {z | (matHom _ σ J m).1 *ᵥ z ∈ Λ}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, mulVec_add] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a z hz => by
        have e : (matHom _ σ J m).1 *ᵥ (a • z) = a • ((matHom _ σ J m).1 *ᵥ z) := by
          change (matHom _ σ J m).1 *ᵥ ((a : Fv F v ⊗[F] E) • z) = (a : Fv F v ⊗[F] E) • ((matHom _ σ J m).1 *ᵥ z)
          rw [mulVec_smul]
        change (matHom _ σ J m).1 *ᵥ (a • z) ∈ Λ
        rw [e]
        exact Λ.smul_mem a hz }
  have hL' : ∀ z, z ∈ L' ↔ (matHom _ σ J m).1 *ᵥ z ∈ Λ := fun z => Iff.rfl
  have hev : IsEvenInt (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) L' := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · rw [← hR_isom m a b]
      exact hint _ ha _ hb
    · rw [← hR_isom m a a]
      exact heven _ ha
  have hle : L' ≤ Λ := hmax L' hev hsub
  exact fun y => ⟨hsub y, fun h => hle h⟩

end GlobalTheory.CompanionTheory.KFin.GoodLocal

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeRankOneSplit
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin.RankOne

section

variable {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V]

theorem h_smul_smul {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (r r' : R) (w : V) :
    h (r • w) (r' • w) = r' * (c r * c (h w w)) := by
  rw [hh.smul_right, hh.symm w (r • w), hh.smul_right, map_mul]

theorem phi_h {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (φ : R ≃+* k × k)
    (hc : ∀ r, φ (c r) = (φ r).swap) (r r' : R) (w : V) (δ : k) (hd : φ (h w w) = (δ, δ)) :
    φ (h (r • w) (r' • w)) = ((φ r').1 * (φ r).2 * δ, (φ r').2 * (φ r).1 * δ) := by
  rw [h_smul_smul hh, map_mul, map_mul, hc, hc, hd]
  ext <;> simp [mul_assoc]

theorem smul_eq_zero_of_unit {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (w : V)
    (hu : IsUnit (h w w)) (r : R) (h0 : r • w = 0) : r = 0 := by
  have h1 := hh.smul_right r w w
  have h2 := hh.smul_right 0 w w
  rw [h0] at h1
  rw [zero_smul, zero_mul] at h2
  rw [h2] at h1
  exact hu.mul_left_eq_zero.1 h1.symm

theorem span_comp_false (p : R →+* k) {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (w : V)
    (hu : IsUnit (h w w)) (𝔬 : Subring R) (L : Submodule 𝔬 V)
    (hspan : Submodule.span R (L : Set V) = ⊤) (hL : ∀ x ∈ L, ∃ r : R, x = r • w ∧ p r = 0) : False := by
  let S : Submodule R V :=
    { carrier := {x | ∃ r : R, x = r • w ∧ p r = 0}
      add_mem' := by
        rintro _ _ ⟨r, rfl, hr⟩ ⟨s, rfl, hs⟩
        exact ⟨r + s, (add_smul _ _ _).symm, by simp [hr, hs]⟩
      zero_mem' := ⟨0, (zero_smul _ _).symm, map_zero p⟩
      smul_mem' := by
        rintro a _ ⟨r, rfl, hr⟩
        exact ⟨a * r, (mul_smul _ _ _).symm, by simp [hr]⟩ }
  have hle : Submodule.span R (L : Set V) ≤ S := Submodule.span_le.2 fun x hx => hL x hx
  rw [hspan] at hle
  obtain ⟨r, hr, h0⟩ : w ∈ S := hle Submodule.mem_top
  have h1 : (1 - r) • w = 0 := by rw [sub_smul, one_smul, ← hr, sub_self]
  have h2 : r = 1 := (sub_eq_zero.1 (smul_eq_zero_of_unit hh w hu _ h1)).symm
  rw [h2, map_one] at h0
  exact one_ne_zero h0

def lat (O : ValuationSubring k) (φ : R ≃+* k × k) (𝔬 : Subring R)
    (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) (w : V) (a b : k) : Submodule 𝔬 V where
  carrier := {v | ∃ r : R, v = r • w ∧ (∃ x ∈ O, (φ r).1 = a * x) ∧ ∃ y ∈ O, (φ r).2 = b * y}
  add_mem' := by
    rintro _ _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩ ⟨s, rfl, ⟨x', hx', h1'⟩, y', hy', h2'⟩
    exact ⟨r + s, (add_smul _ _ _).symm, ⟨x + x', O.add_mem _ _ hx hx', by simp [h1, h1', mul_add]⟩,
      y + y', O.add_mem _ _ hy hy', by simp [h2, h2', mul_add]⟩
  zero_mem' := ⟨0, (zero_smul _ _).symm, ⟨0, O.zero_mem, by simp⟩, 0, O.zero_mem, by simp⟩
  smul_mem' := by
    rintro ⟨s, hs⟩ _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩
    obtain ⟨hs1, hs2⟩ := (h𝔬 s).1 hs
    refine ⟨s * r, ?_, ⟨(φ s).1 * x, O.mul_mem _ _ hs1 hx, ?_⟩, (φ s).2 * y, O.mul_mem _ _ hs2 hy, ?_⟩
    · rw [mul_smul]; rfl
    · simp only [map_mul, Prod.fst_mul, h1]; ring
    · simp only [map_mul, Prod.snd_mul, h2]; ring

theorem lat_even {O : ValuationSubring k} {φ : R ≃+* k × k} {c : R →+* R} {𝔬 : Subring R}
    (hc : ∀ r, φ (c r) = (φ r).swap) (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O)
    {h : V → V → R} (hh : IsHerm c h) (w : V) (δ : k) (hd : φ (h w w) = (δ, δ)) (a b : k)
    (hab : a * b * δ = 1) : IsEvenInt c 𝔬 h (lat O φ 𝔬 h𝔬 w a b) := by
  constructor
  · rintro _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩ _ ⟨r', rfl, ⟨x', hx', h1'⟩, y', hy', h2'⟩
    rw [h𝔬, phi_h hh φ hc r r' w δ hd, h1, h2, h1', h2']
    constructor
    · have : a * x' * (b * y) * δ = x' * y := by
        calc a * x' * (b * y) * δ = (a * b * δ) * (x' * y) := by ring
          _ = x' * y := by rw [hab, one_mul]
      simpa [this] using O.mul_mem _ _ hx' hy
    · have : b * y' * (a * x) * δ = y' * x := by
        calc b * y' * (a * x) * δ = (a * b * δ) * (y' * x) := by ring
          _ = y' * x := by rw [hab, one_mul]
      simpa [this] using O.mul_mem _ _ hy' hx
  · rintro _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩
    have hxy : (φ r).1 * (φ r).2 * δ = x * y := by
      rw [h1, h2]
      calc a * x * (b * y) * δ = (a * b * δ) * (x * y) := by ring
        _ = x * y := by rw [hab, one_mul]
    refine ⟨φ.symm (x * y, 0), ?_, ?_⟩
    · rw [h𝔬]
      simpa using O.mul_mem _ _ hx hy
    · apply φ.injective
      rw [phi_h hh φ hc r r w δ hd, map_add (f := _), hc]
      simp only [RingEquiv.apply_symm_apply]
      ext
      · simpa using hxy
      · simpa [mul_comm (φ r).1 (φ r).2] using (by rw [mul_comm (φ r).2 (φ r).1]; exact hxy : (φ r).2 * (φ r).1 * δ = x * y)

end

theorem unimodular_coords : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V] (O : ValuationSubring k) (φ : R ≃+* k × k) (c : R →+* R) (𝔬 : Subring R), (∀ r, φ (c r) = (φ r).swap) → (∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) → ∀ h : V → V → R, IsHerm c h → ∀ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) → IsUnit (h w₀ w₀) → ∀ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → ∀ α β : k, (∀ r : R, r • w₀ ∈ L ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y)) → α ≠ 0 ∧ β ≠ 0 ∧ ∃ u : k, u ∈ O ∧ u⁻¹ ∈ O ∧ α * β * (φ (h w₀ w₀)).1 = u := by
  intro k R V _ _ _ _ O φ c 𝔬 hc h𝔬 h hh w₀ hw hu L hL α β hmem
  obtain ⟨⟨_, hspan⟩, ⟨hint, _⟩, hmax⟩ := hL
  have hcd : c (h w₀ w₀) = h w₀ w₀ := (hh.symm w₀ w₀).symm
  obtain ⟨δ, hd⟩ : ∃ δ, φ (h w₀ w₀) = (δ, δ) := by
    have h1 := hc (h w₀ w₀)
    rw [hcd] at h1
    exact ⟨(φ (h w₀ w₀)).1, Prod.ext rfl (congrArg Prod.fst h1).symm⟩
  have hδ : δ ≠ 0 := by
    have h1 : IsUnit (φ (h w₀ w₀)) := hu.map φ
    rw [hd, Prod.isUnit_iff] at h1
    exact h1.1.ne_zero
  have hα : α ≠ 0 := by
    rintro rfl
    refine span_comp_false ((RingHom.fst k k).comp (φ : R →+* k × k)) hh w₀ hu 𝔬 L hspan fun x hx => ?_
    obtain ⟨r, rfl⟩ := hw x
    obtain ⟨⟨y, _, hy⟩, _⟩ := (hmem r).1 hx
    exact ⟨r, rfl, by simpa using hy⟩
  have hβ : β ≠ 0 := by
    rintro rfl
    refine span_comp_false ((RingHom.snd k k).comp (φ : R →+* k × k)) hh w₀ hu 𝔬 L hspan fun x hx => ?_
    obtain ⟨r, rfl⟩ := hw x
    obtain ⟨_, ⟨y, _, hy⟩⟩ := (hmem r).1 hx
    exact ⟨r, rfl, by simpa using hy⟩
  refine ⟨hα, hβ, ?_⟩
  have hγ0 : α * β * δ ≠ 0 := mul_ne_zero (mul_ne_zero hα hβ) hδ
  have hγ : α * β * δ ∈ O := by
    have h1 : φ.symm (α, 0) • w₀ ∈ L :=
      (hmem _).2 ⟨⟨1, O.one_mem, by simp⟩, 0, O.zero_mem, by simp⟩
    have h2 : φ.symm (0, β) • w₀ ∈ L :=
      (hmem _).2 ⟨⟨0, O.zero_mem, by simp⟩, 1, O.one_mem, by simp⟩
    have h3 := (h𝔬 _).1 (hint _ h1 _ h2)
    rw [phi_h hh φ hc _ _ w₀ δ hd] at h3
    have h4 := h3.2
    simp only [RingEquiv.apply_symm_apply] at h4
    rwa [mul_comm β α] at h4
  have hab : α / (α * β * δ) * β * δ = 1 := by
    field_simp
  have hle : L ≤ lat O φ 𝔬 h𝔬 w₀ (α / (α * β * δ)) β := by
    intro v hv
    obtain ⟨r, rfl⟩ := hw v
    obtain ⟨⟨x, hx, h1⟩, y, hy, h2⟩ := (hmem r).1 hv
    refine ⟨r, rfl, ⟨α * β * δ * x, O.mul_mem _ _ hγ hx, ?_⟩, y, hy, h2⟩
    rw [h1]
    field_simp
  have hL₂ := hmax _ (lat_even hc h𝔬 hh w₀ δ hd _ _ hab) hle
  have hmem₂ : φ.symm (α / (α * β * δ), 0) • w₀ ∈ lat O φ 𝔬 h𝔬 w₀ (α / (α * β * δ)) β :=
    ⟨_, rfl, ⟨1, O.one_mem, by simp⟩, 0, O.zero_mem, by simp⟩
  obtain ⟨⟨x, hx, h1⟩, _⟩ := (hmem _).1 (hL₂ hmem₂)
  simp only [RingEquiv.apply_symm_apply] at h1
  refine ⟨α * β * δ, hγ, ?_, ?_⟩
  · have h2 : (α * β * δ)⁻¹ = x := by
      apply mul_left_cancel₀ hα
      rw [← h1, div_eq_mul_inv]
    rwa [h2]
  · rw [hd]

end GlobalTheory.CompanionTheory.KFin.RankOne
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableLocalZeroCount
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton.Chart

theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {A : Set X} (hA : IsSigmaCompact A) :
    MeasurableSet A := by
  obtain ⟨K, hK, rfl⟩ := hA
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

variable {Y : Var ℂ} {L : LB Y.X}

noncomputable def chartVal {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (j : Fin n) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) : ℂ :=
  secVal Y.str (RingHom.id ℂ) (b j) i (c.e.symm v)

theorem encard_eq_zeroCnt {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (C : Fin Y.dim → Fin n → ℂ) :
    (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) =
      zeroCnt Y.dim (c.e '' A) (chartVal b c i) C := by
  have hinj : Set.InjOn c.e {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} :=
    c.e.injOn.mono fun y hy => hAc hy.1
  have himg : c.e '' {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} =
      {z ∈ c.e '' A | ∀ k, ∑ j, C k j * chartVal b c i j z = 0} := by
    ext v
    constructor
    · rintro ⟨y, ⟨hyA, hy⟩, rfl⟩
      refine ⟨⟨y, hyA, rfl⟩, fun k => ?_⟩
      simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k i (hAi hyA)
    · rintro ⟨⟨y, hyA, rfl⟩, hy⟩
      refine ⟨y, ⟨hyA, fun k i' hi' => ?_⟩, rfl⟩
      have h0 : ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0 := by
        simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k
      have e : ∀ j, secVal Y.str (RingHom.id ℂ) (b j) i' y =
          gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y :=
        fun j => (secVal_mem (b j)).1 i' i y hi' (hAi hyA)
      simp only [e]
      calc ∑ j, C k j * (gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y)
          = gv Y.str (RingHom.id ℂ) L i' i y *
              ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [h0, mul_zero]
  rw [zeroCnt, ← himg, hinj.encard_image]

theorem fsBasis_φ_chart (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤)
    (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).φ i (c.e.symm v) =
      Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) := by
  rw [Weight.fsBasis_φ]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rfl

theorem chernPart_eq_lintegral (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι)
    (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAm : MeasurableSet A) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (hBm : MeasurableSet (c.e '' A)) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A =
      ∫⁻ z in c.e '' A, ENNReal.ofReal ((Y.dim.factorial : ℝ) / Real.pi ^ Y.dim *
        (ReciprocityTheory.L2DbarEstimates.cHess Y.dim
          (fun v => ((Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  have hC := Weight.isCInf_fsBasis (p := Y.str) (σ := RingHom.id ℂ) hL b hb 1 (by simp)
  rw [Weight.chernPart_apply hC 1 c hAm hAc]
  refine setLIntegral_congr_fun hBm fun v hv => ?_
  obtain ⟨y, hy, rfl⟩ := hv
  have hys := c.e.left_inv (hAc hy)
  simp only [hys]
  rw [c.chernDens_eq hC (hAc hy) (hAi hy), AlgChart.hess]
  simp only [fsBasis_φ_chart hL b hb c i, Units.val_one, Int.cast_one, one_mul]

end GlobalTheory.CompanionTheory.FSCrofton.Chart


open GlobalTheory.CompanionTheory.FSCrofton.Chart in
theorem GlobalTheory.CompanionTheory.FSCrofton.crofton_chart : ∀ (Y : Var ℂ) (L : LB Y.X) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (j₀ : Fin n) (A : Set (CxPts Y.str (RingHom.id ℂ))), A ⊆ c.e.source → A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (∀ y ∈ A, secVal Y.str (RingHom.id ℂ) (b j₀) i y ≠ 0) → IsSigmaCompact A → Measurable (fun C : Fin Y.dim → Fin n → ℂ => (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞)) ∧ ∫⁻ C : Fin Y.dim → Fin n → ℂ, gW Y.dim (Fin n) C * (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (Real.pi ^ (Y.dim * n)) * (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A := by
  intro Y L hL n b hb c i j₀ A hAc hAi hA0 hAs
  have hAm : MeasurableSet A := measurableSet_of_isSigmaCompact hAs
  have hBs : IsSigmaCompact (c.e '' A) :=
    hAs.image_of_continuousOn (c.e.continuousOn.mono hAc)
  have hBm : MeasurableSet (c.e '' A) := measurableSet_of_isSigmaCompact hBs
  have hcnt := encard_eq_zeroCnt b c i A hAc hAi

  set W : Y.X.Opens := L.U i ⊓ nonzeroLocus (b j₀) with hW
  set U : Set (ReciprocityTheory.L2DbarEstimates.V Y.dim) := c.e.target ∩ c.e.symm ⁻¹' ptsIn Y.str (RingHom.id ℂ) W
    with hU
  have hUo : IsOpen U := ChartGlue.isOpen_over c.e (isOpen_ptsIn W)
  have hUi : ∀ v ∈ U, c.e.symm v ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) := fun v hv =>
    (mem_ptsIn_inf.1 hv.2).1
  have hd : ∀ j, DifferentiableOn ℂ (chartVal b c i j) U := fun j =>
    (c.holo (L.U i) ((b j).f i)).mono fun v hv => ⟨hv.1, hUi v hv⟩
  have h0 : ∀ z ∈ U, chartVal b c i j₀ z ≠ 0 := fun z hz =>
    (secVal_ne_zero_iff (b j₀) (hUi z hz)).2 (mem_ptsIn_inf.1 hz.2).2
  have hBU : c.e '' A ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨c.e.map_source (hAc hy), ?_⟩
    change c.e.symm (c.e y) ∈ ptsIn Y.str (RingHom.id ℂ) W
    rw [c.e.left_inv (hAc hy)]
    exact mem_ptsIn_inf.2 ⟨hAi hy, (secVal_ne_zero_iff (b j₀) (hAi hy)).1 (hA0 y hy)⟩
  refine ⟨?_, ?_⟩
  · simp only [hcnt]
    exact _root_.GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt Y.dim (Fin n) U (c.e '' A) (chartVal b c i)
      (fun j => (hd j).continuousOn) hBU hBs
  · simp only [hcnt]
    have key := _root_.GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.crofton_local Y.dim (Fin n) j₀ U (c.e '' A) (chartVal b c i) hUo hd h0 hBU hBs
    rw [key, Fintype.card_fin, chernPart_eq_lintegral hL b hb c i A hAm hAc hAi hBm]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_single_nonzero_factor_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (Y : Fin h → IrrGL (k := k)) (hd : ∑ a, (Y a).1 = N) (i₀ : Fin h), (∀ i, i ≠ i₀ → (Y i).1 = 0) → ∃ z : IrrCl (GL (Fin N) k), (⟨N, z⟩ : IrrGL (k := k)) = Y i₀ ∧ Nonempty ((prodIrr Y hd).Equiv z.rep.ρ) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single | exact GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single | (intros; apply GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single <;> assumption)
end

