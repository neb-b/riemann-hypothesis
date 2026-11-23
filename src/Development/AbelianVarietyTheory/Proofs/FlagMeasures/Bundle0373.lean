module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFamilyUnitriangularChangeOfMemFrameUnipotent
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.NFrameTri

section Gen

variable {K : Type} [CommRing K] {W : Type} [AddCommGroup W] [Module K W] {m : ℕ}

def flag (K : Type) [CommRing K] [Module K W] (f : Fin m → W) (j : ℕ) : Submodule K W :=
  Submodule.span K (f '' {a | a.val < j})

lemma flag_mono (f : Fin m → W) {i j : ℕ} (h : i ≤ j) : flag K f i ≤ flag K f j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

lemma flag_zero (f : Fin m → W) : flag K f 0 = ⊥ := by
  simp [flag]

def Lowers (f : Fin m → W) (n : W ≃ₗ[K] W) : Prop :=
  ∀ j, ∀ v ∈ flag K f (j + 1), n v - v ∈ flag K f j

lemma lowers_of_gen (f : Fin m → W) (n : W ≃ₗ[K] W)
    (h : ∀ b : Fin m, n (f b) - f b ∈ flag K f b.val) : Lowers f n := by
  intro j v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact flag_mono f (Nat.lt_succ_iff.mp hb) (h b)
  | zero => simp
  | add x y _ _ hx hy =>
    have : n (x + y) - (x + y) = (n x - x) + (n y - y) := by rw [map_add (f := _)]; abel
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    have : n (c • x) - c • x = c • (n x - x) := by rw [map_smul, smul_sub]
    rw [this]; exact Submodule.smul_mem _ c hx

lemma Lowers.mul {f : Fin m → W} {n n' : W ≃ₗ[K] W} (h : Lowers f n) (h' : Lowers f n') :
    Lowers f (n * n') := by
  intro j v hv
  have h1 := h' j v hv
  have h2 : n' v ∈ flag K f (j + 1) := by
    have : n' v = (n' v - v) + v := by abel
    rw [this]; exact add_mem (flag_mono f (Nat.le_succ j) h1) hv
  have : (n * n') v - v = (n (n' v) - n' v) + (n' v - v) := by
    rw [LinearEquiv.mul_apply]; abel
  rw [this]; exact add_mem (h j _ h2) h1

lemma Lowers.surj {f : Fin m → W} {n : W ≃ₗ[K] W} (h : Lowers f n) :
    ∀ j, ∀ v ∈ flag K f j, ∃ w ∈ flag K f j, n w = v := by
  intro j
  induction j with
  | zero =>
    intro v hv
    rw [flag_zero, Submodule.mem_bot] at hv
    exact ⟨0, zero_mem _, by simp [hv]⟩
  | succ j ih =>
    intro v hv
    obtain ⟨w, hw, e⟩ := ih _ (h j v hv)
    refine ⟨v - w, sub_mem hv (flag_mono f (Nat.le_succ j) hw), ?_⟩
    rw [map_sub, e]; abel

lemma Lowers.inv {f : Fin m → W} {n : W ≃ₗ[K] W} (h : Lowers f n) : Lowers f n⁻¹ := by
  intro j v hv
  obtain ⟨w, hw, rfl⟩ := h.surj _ v hv
  have e : n⁻¹ (n w) = w := n.symm_apply_apply w
  have : n⁻¹ (n w) - n w = -(n w - w) := by rw [e]; abel
  rw [this]; exact neg_mem (h j w hw)

lemma exists_coef (f : Fin m → W) (j : ℕ) (v : W) (hv : v ∈ flag K f j) :
    ∃ c : Fin m → K, (∀ a, j ≤ a.val → c a = 0) ∧ v = ∑ a, c a • f a := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨Pi.single b 1, fun a ha => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hb (not_lt.mpr ha)
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun a ha => by simp [hc a ha, hd a ha], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul s x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨s • c, fun a ha => by simp [hc a ha], by simp [Finset.smul_sum, smul_smul]⟩

lemma Lowers.tri {f : Fin m → W} {n : W ≃ₗ[K] W} (h : Lowers f n) : Tri K f (fun b => n (f b)) := by
  have : ∀ b : Fin m, ∃ c : Fin m → K, (∀ a, b.val ≤ a.val → c a = 0) ∧ n (f b) - f b = ∑ a, c a • f a :=
    fun b => exists_coef f _ _ (h b.val (f b) (Submodule.subset_span ⟨b, Nat.lt_succ_self _, rfl⟩))
  choose c hc e using this
  refine ⟨Matrix.of fun a b => c b a + if a = b then 1 else 0, ⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
  · simp [hc b a hab.le, hab.ne']
  · simp [hc a a le_rfl]
  · simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ← e]
    simp

end Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma Fj_le_flag {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) (j : ℕ) : Fr.Fj j ≤ flag E Fr.f j := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.castSucc, ha, rfl⟩

lemma last_mem_perp {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) :
    Fr.f (Fin.last r) ∈ H.perp (H.X Fr.f) := by
  intro x hx
  have : H.h x (Fr.f (Fin.last r)) = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]
  rw [H.h_herm, this, map_zero]

lemma lowers_of_mem_NSet {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.NSet) :
    Lowers Fr.f n := by
  obtain ⟨-, h1, h2⟩ := hn
  apply lowers_of_gen
  intro b
  induction b using Fin.lastCases with
  | last =>
    refine Submodule.span_mono ?_ (h2 _ (last_mem_perp Fr))
    rintro _ ⟨a, rfl⟩
    exact ⟨a.castSucc, a.isLt, rfl⟩
  | cast a =>
    exact Fj_le_flag Fr _ (h1 (a.val + 1) a.isLt (Fr.e a)
      (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩))

theorem tri_of_mem_N (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) :
    ∀ n ∈ Fr.N, Tri E Fr.f (fun b => n (Fr.f b)) := by
  intro n hn
  apply Lowers.tri
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact lowers_of_mem_NSet Fr hx
  | one => intro j v _; simp
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

end GlobalTheory.NFrameTri
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingLeadingMinorEqOfUnitriangularChanges
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.MinorTri

theorem sum_eq_sum_castLE {E : Type} [AddCommMonoid E] {n l : ℕ} (hl : l ≤ n) (φ : Fin n → E)
    (h : ∀ c : Fin n, l ≤ c.val → φ c = 0) : ∑ c, φ c = ∑ c : Fin l, φ (Fin.castLE hl c) := by
  refine (Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
    (fun c : Fin l => φ (Fin.castLE hl c)) φ ?_ (fun _ => rfl)).symm
  intro c hc
  apply h
  by_contra hlt
  exact hc ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩

theorem det_block_uni {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n) (A : Matrix (Fin n) (Fin n) E)
    (hA : Uni A) : (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  obtain ⟨h0, h1⟩ := hA
  rw [Matrix.det_of_upperTriangular]
  · simp [Matrix.submatrix_apply, h1]
  · intro i j hij
    simp only [Matrix.submatrix_apply]
    apply h0
    rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
    exact hij

theorem block_mul_uni {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n) (Z A : Matrix (Fin n) (Fin n) E)
    (hA : Uni A) : (Z * A).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Z.submatrix (Fin.castLE hl) (Fin.castLE hl) * A.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  obtain ⟨h0, -⟩ := hA
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_eq_sum_castLE hl _ ?_]
  intro c hc
  rw [h0 c (Fin.castLE hl j) (by rw [Fin.lt_def, Fin.coe_castLE]; exact lt_of_lt_of_le j.isLt hc), mul_zero]

theorem det_block_mul_uni {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n) (Z A : Matrix (Fin n) (Fin n) E)
    (hA : Uni A) : ((Z * A).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  rw [block_mul_uni hl Z A hA, Matrix.det_mul, det_block_uni hl A hA, mul_one]

theorem det_block_transpose_uni_mul {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n)
    (Z A : Matrix (Fin n) (Fin n) E) (hA : Uni A) :
    ((A.transpose * Z).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : A.transpose * Z = (Z.transpose * A).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e, ← Matrix.transpose_submatrix, Matrix.det_transpose, det_block_mul_uni hl _ _ hA,
    ← Matrix.transpose_submatrix, Matrix.det_transpose]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 := H.h_smul_left 0 0 y
    simpa using h0
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

theorem h_sum_right (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (x : V) :
    H.h x (∑ i ∈ s, c i • v i) = ∑ i ∈ s, M.L.cj (c i) * H.h x (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.h_herm (∑ i ∈ s, c i • v i) x, h_sum_left H, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm (v i) x]

theorem Dl_eq_of_tri (H : HermSp M V) {r : ℕ} (f f' g g' : Fin (r + 1) → V) (hg : Tri E f g)
    (hg' : Tri E f' g') (l : ℕ) : H.Dl g g' l = H.Dl f f' l := by
  obtain ⟨A, hA, hAc⟩ := hg
  obtain ⟨A', hA', hA'c⟩ := hg'
  obtain ⟨hA0, hA1⟩ := hA
  have hB : Uni (A.map M.L.cj) := by
    unfold Uni
    exact ⟨fun a b hab => by simp [Matrix.map_apply, hA0 a b hab], fun a => by simp [Matrix.map_apply, hA1 a]⟩
  have hZ : H.Zhat g g' = (A.map M.L.cj).transpose * H.Zhat f f' * A' := by
    ext a b
    simp only [HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [hAc a, hA'c b, h_sum_left H]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [h_sum_right H, mul_comm]
  unfold HermSp.Dl
  split_ifs with hl
  · rw [hZ, det_block_mul_uni hl _ A' hA', det_block_transpose_uni_mul hl _ _ hB]
  · rfl

end GlobalTheory.MinorTri
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatible
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm.CompatPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem fixedFrameOfWord_isotropic_eq_flag : (F0 X u).X = (X.Fu u).X := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa FlagG.X
  congr 1
  ext x
  constructor
  · rintro ⟨b, -, rfl⟩; exact ⟨b, (fv_cast _ b).symm⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, b.2, fv_cast _ b⟩

theorem compatC : CompatC := by
  rintro D X Y u ⟨s₁, s₂⟩ ⟨-, -, hp⟩
  have hp' : rowOf Y.TR (Y.cs u) (Y.cs u) s₁ = rowOf Y.TR (Y.cs u) (Y.cs u) s₂ := hp
  have hl : s₁.lam = s₂.lam := congrArg (fun r => r.1.1) hp'
  have hl' : s₁.lam' = s₂.lam' := congrArg (fun r => r.2.1.1) hp'
  have hi : iotaOf Y.TR (Y.cs u) (Y.cs u) s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u) s₂ := congrArg (fun r => r.2.2) hp'
  have h := (Formalism.L2.SG.Pf.Act.ratIotaC' Y u u s₁ s₂ hl hl').1 (Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ hl hl' hi)
  refine ⟨hl, hl', fun x hx => ?_⟩
  have hx2 : x ∈ GlobalTheory.HermLat.perp (HV D) (F0 X u).X := hx.2
  rw [GlobalTheory.HermLat.mem_perp_iff, fixedFrameOfWord_isotropic_eq_flag] at hx2
  have hx' : x ∈ Lrep s₁.lam (lf D (X.Fu u)) := by
    refine ⟨hx.1, ?_⟩
    show x ∈ orth (VS D) (X.Fu u).X
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    exact hx2
  have h2 := h x hx'
  unfold NgX at h2
  rw [sup_assoc, sup_idem] at h2
  rw [fixedFrameOfWord_isotropic_eq_flag]
  refine SetLike.le_def.1 (sup_le_sup ?_ le_rfl) h2
  rw [Submodule.ideal_span_singleton_smul]
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩
end GlobalTheory.TypeAsm.CompatPf
end
end

