module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0055

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviInfUnipotentLeHermitianPart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev adV {n : ℕ} (v : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (v i)

theorem adMat_mulVec {a c : ℕ} (M : Matrix (Fin a) (Fin c) E) (v : Fin c → E) :
    adMat F M *ᵥ adV (F := F) v = adV (F := F) (M *ᵥ v) :=
  funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) M v i).symm

theorem core (σ : E →ₐ[F] E) {n n' r r' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
    {X : Matrix (Fin n) (Fin r) E} {X' Y' : Matrix (Fin n') (Fin r') E} {T : Finset (Fin r)} {e : Fin r' → Fin r}
    {I : Matrix (Fin n) (Fin n') E} {P : Matrix (Fin n') (Fin n) E}
    (hmono : StrictMono e) (hrange : ∀ i, i ∉ upTo T ↔ i ∈ Set.range e)
    (hIX : I * X' = X.submatrix id e) (hPI : P * I = 1)
    (hg : Formalism.UG.cT (σ : E →+* E) I * J = J' * P)
    (hPl : ∀ l ∈ upTo T, P *ᵥ Xᵀ l = 0)
    (hperp : ∀ x, ∀ l ∈ upTo T, ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (I *ᵥ x)) l = 0)
    (hW' : IsWittFrame σ J' X' Y') (k : Fin r') (g : GAd σ J) (b : GAd σ J')
    (hmat : (matHom _ σ J g).1 = 1 + adMat F I * ((matHom _ σ J' b).1 - 1) * adMat F P)
    (hgm : g ∈ unip σ J X (insert (e k) T)) : b ∈ unip σ J' X' {k} := by
  obtain ⟨M, hM⟩ : ∃ M, M = (matHom _ σ J' b).1 - 1 := ⟨_, rfl⟩
  rw [← hM] at hmat
  have hPI' : adMat F P * adMat F I = 1 := by
    rw [← Matrix.map_mul, hPI, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPIv : ∀ w, adMat F P *ᵥ (adMat F I *ᵥ w) = w := fun w => by rw [mulVec_mulVec, hPI', one_mulVec]
  have hGv : ∀ w, (matHom _ σ J g).1 *ᵥ (adMat F I *ᵥ w) - adMat F I *ᵥ w = adMat F I *ᵥ (M *ᵥ w) := fun w => by
    rw [hmat, Matrix.add_mulVec, one_mulVec, add_sub_cancel_left, ← Matrix.mulVec_mulVec, hPIv, ← Matrix.mulVec_mulVec]
  have hXe : ∀ i, (adMat F X)ᵀ (e i) = adMat F I *ᵥ (adMat F X')ᵀ i := fun i => by
    have h : adMat F I * adMat F X' = adMat F (X.submatrix id e) := by rw [← Matrix.map_mul, hIX]
    funext j
    exact (congrFun (congrFun h j) i).symm
  have hPX : ∀ l ∈ upTo T, adMat F P *ᵥ (adMat F X)ᵀ l = 0 := fun l hl => by
    change adMat F P *ᵥ adV (F := F) (Xᵀ l) = 0
    rw [adMat_mulVec, hPl l hl]
    funext i
    exact map_zero _
  have hPspan : ∀ (A : Set (Fin r)) (N : Submodule (AF F ⊗[F] E) (Fin n' → AF F ⊗[F] E)),
      (∀ i ∈ A, adMat F P *ᵥ (adMat F X)ᵀ i ∈ N) → ∀ y ∈ colSpan F X A, adMat F P *ᵥ y ∈ N := fun A N h y hy => by
    have h1 : colSpan F X A ≤ N.comap (adMat F P).mulVecLin :=
      Submodule.span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact h i hi)
    exact h1 hy
  have ha : ∀ i : Fin r', i ≤ k → M *ᵥ (adMat F X')ᵀ i = 0 := fun i hi => by
    have h1 := (Subgroup.mem_iInf.1 hgm.1 (e i)).2 ((adMat F X)ᵀ (e i)) (Submodule.subset_span ⟨e i, rfl, rfl⟩)
    rw [hXe, hGv] at h1
    have h2 := hPspan _ ⊥ (fun l hl => by
      obtain ⟨k', hk', hlk, hkj⟩ := hl
      rcases Finset.mem_insert.1 hk' with rfl | h
      · exact absurd hkj (not_lt.2 (hmono.monotone hi))
      · exact (Submodule.mem_bot _).2 (hPX l ⟨k', h, hlk⟩)) _ h1
    rw [hPIv] at h2
    exact (Submodule.mem_bot _).1 h2
  have hfix : M * adMat F (initCols X' k) = 0 := Matrix.ext_col fun i =>
    ha (i.castLE k.2) (Nat.le_of_lt_succ i.2)
  have c1 : ∀ {a c : ℕ} (Z : Matrix (Fin a) (Fin c) E), Formalism.UG.cT (sigR (AF F) σ) (adMat F Z) = adMat F (Formalism.UG.cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have fix : (matHom _ σ J' b).1 * adMat F (initCols X' k) = adMat F (initCols X' k) := by
    rw [hM, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hfix
    exact hfix
  rw [unip_singleton hW' k]
  apply Subgroup.subset_closure
  refine ⟨hM ▸ hfix, ?_, fun x hx => ?_⟩
  · have hu : Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J' b).1 * adMat F J' * (matHom _ σ J' b).1 = adMat F J' := b.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, adMat, Matrix.map_mul]
    change adMat F _ * adMat F J' * _ = adMat F _ * adMat F J'
    conv_lhs => rw [← c1, ← fix, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F J'), hu, c1]
  · have h5 : Formalism.UG.cT (σ : E →+* E) (X.submatrix id e) * J * I = Formalism.UG.cT (σ : E →+* E) X' * J' := by
      rw [← hIX, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ J, hg, Matrix.mul_assoc, hPI,
        Matrix.mul_one]
    have hle : ∀ l, l ∉ upTo T → (∃ k' ∈ insert (e k) T, l ≤ k') → ∃ i, i ≤ k ∧ e i = l := fun l hl ⟨k', hk', hlk⟩ => by
      obtain ⟨i, rfl⟩ := (hrange l).1 hl
      rcases Finset.mem_insert.1 hk' with rfl | h
      · exact ⟨i, hmono.le_iff_le.1 hlk, rfl⟩
      · exact absurd ⟨k', h, hlk⟩ hl
    have hz : ∀ l, (∃ k' ∈ insert (e k) T, l ≤ k') → ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (I *ᵥ x)) l = 0 := fun l hl => by
      by_cases h : l ∈ upTo T
      · exact hperp x l h
      · obtain ⟨i, hi, rfl⟩ := hle l h hl
        rw [mulVec_mulVec]
        have h6 : ((Formalism.UG.cT (σ : E →+* E) X * J * I) *ᵥ x) (e i) = ((Formalism.UG.cT (σ : E →+* E) (X.submatrix id e) * J * I) *ᵥ x) i := rfl
        rw [h6, h5]
        exact congrFun hx ⟨i.val, Nat.lt_succ_of_le hi⟩
    have hp : adV (F := F) (I *ᵥ x) ∈ colPerp σ J X {i | ∃ k' ∈ insert (e k) T, i ≤ k'} := by
      simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
      intro l hl
      change (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ adV (F := F) (I *ᵥ x)) l = 0
      rw [adMat_mulVec]
      change inclR (F := F) (AF F) _ = 0
      rw [hz l hl]
      exact map_zero _
    have h3 := hgm.2.2 _ hp
    rw [← adMat_mulVec, hGv] at h3
    have h4 := hPspan _ (colSpan F X' {i | i ≤ k}) (fun l hl => by
      by_cases h : l ∈ upTo T
      · rw [hPX l h]
        exact zero_mem _
      · obtain ⟨i, hi, rfl⟩ := hle l h hl
        rw [hXe, hPIv]
        exact Submodule.subset_span ⟨i, hi, rfl⟩) _ h3
    rw [hPIv] at h4
    obtain ⟨a, ha'⟩ := mem_colSpan_iff.1 h4
    exact ⟨a, by rw [← hM]; exact ha'.symm⟩

end Core

theorem mem_unip_of_image : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b : GA D V', s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) → b ∈ unip D.sp.cm.sig V'.gram X' {k} := by
  intro D V m X Y hW T V' ι hι hR m' e X' Y' hS hW' s hs k b hb
  obtain ⟨hmono, hrange, hIX, -⟩ := hS
  refine core D.sp.cm.sig hmono hrange hIX (prM_mul_frameMat hι) cT_frameMat_mul_gram (fun l hl => ?_) (fun x l hl => ?_)
    hW' k (s b) b (mat_eq hι hs b) hb
  · exact prM_mulVec_eq_zero fun v' => ((hR (ι v')).1 ⟨v', rfl⟩ l hl).1
  · have hv : ι (V'.frame.equivFun.symm x) = V.frame.equivFun.symm (frameMat V V' ι *ᵥ x) := by
      apply V.frame.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      have h := LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (V'.frame.equivFun.symm x)
      have h' : V'.frame.repr (V'.frame.equivFun.symm x) = x := funext fun i => repr_symm V' x i
      rw [h'] at h
      exact h.symm
    have h := ((hR (ι (V'.frame.equivFun.symm x))).1 ⟨_, rfl⟩ l hl).1
    rw [hv, hT_frame] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_) h
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedAutomorphicInvariance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU

open Formalism.UG (cT)

section Abstract

variable {R : Type} [CommRing R] {a b : ℕ}

theorem eq_zero_of_mem_span_cols {L : Matrix (Fin b) (Fin a) R} {C : Matrix (Fin a) (Fin b) R} (hLC : L * C = 1)
    {I : Set (Fin b)} {w : Fin a → R} (hw : w ∈ Submodule.span R ((fun i => Cᵀ i) '' I))
    (h0 : ∀ i ∈ I, (L *ᵥ w) i = 0) : w = 0 := by
  classical
  have key : ∀ v ∈ Submodule.span R ((fun i => Cᵀ i) '' I), ∃ c : Fin b → R, (∀ i, i ∉ I → c i = 0) ∧ v = C *ᵥ c := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v h =>
      obtain ⟨i, hi, rfl⟩ := h
      refine ⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne (by rintro rfl; exact hi' hi) _, ?_⟩
      rw [mulVec_single_one]
      rfl
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by rw [mulVec_add]⟩
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨t • c, fun i hi => by simp [hc i hi], by rw [mulVec_smul]⟩
  obtain ⟨c, hc, rfl⟩ := key w hw
  have e : L *ᵥ (C *ᵥ c) = c := by rw [mulVec_mulVec, hLC, one_mulVec]
  rw [e] at h0
  have : c = 0 := funext fun i => by
    by_cases hi : i ∈ I
    · exact h0 i hi
    · exact hc i hi
  rw [this, mulVec_zero]

theorem mul_eq_of_conj (s : R →+* R) {G H A : Matrix (Fin a) (Fin a) R} {C : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin b) R} (hHG : H * G = 1) (hU : cT s H * A * H = A) (hHC : H * C = C * B) :
    cT s C * A * G = cT s B * (cT s C * A) := by
  calc cT s C * A * G = cT s C * (cT s H * A * H) * G := by rw [hU]
    _ = cT s (H * C) * A * (H * G) := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT s B * (cT s C * A) := by
      rw [hHC, hHG, Formalism.UG.cT_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem mul_eq_self_of_pair (s : R →+* R) {G A : Matrix (Fin a) (Fin a) R} {C D : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin b) R} (hU : cT s G * A * G = A) (hCD : cT s C * A * D = 1) (hGC : G * C = C)
    (hGD : G * D = D * B) : G * D = D := by
  have hB : B = 1 := by
    calc B = cT s C * A * D * B := by rw [hCD, Matrix.one_mul]
      _ = cT s (G * C) * A * (G * D) := by rw [hGC, hGD]; simp only [Matrix.mul_assoc]
      _ = cT s C * (cT s G * A * G) * D := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hCD]
  rw [hGD, hB, Matrix.mul_one]

end Abstract

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem mat_inv_mul (g : GAd σ J) : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem adMat_mul_eq_one {a b : ℕ} {L : Matrix (Fin a) (Fin b) E} {C : Matrix (Fin b) (Fin a) E} (h : L * C = 1) :
    adMat F L * adMat F C = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cT_initCols_mul (C : Matrix (Fin n) (Fin r) E) (k : Fin r) :
    cT (sigR (AF F) σ) (adMat F (initCols C k)) * adMat F J =
      (adMat F (cT (σ : E →+* E) C * J)).submatrix (Fin.castLE k.2) id := by
  have c1 : cT (sigR (AF F) σ) (adMat F (initCols C k)) = adMat F (cT (σ : E →+* E) (initCols C k)) := rfl
  rw [c1, ← Matrix.map_mul]
  rfl

theorem exists_height_lower_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)} {κ : Fin r}
    (hκ : κ ∉ upTo T) {g : GAd σ J} (hl : g ∈ levi σ J X Y T) (hu : g ∈ unip σ J X (insert κ T)) {j : Fin r}
    (hj : j ∈ upTo T) : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j = (adMat F X)ᵀ j := by
  have hκj : j < κ := by
    obtain ⟨k, hk, hjk⟩ := hj
    by_contra hc
    exact hκ ⟨k, hk, (not_lt.1 hc).trans hjk⟩
  have h1 := (Subgroup.mem_iInf.1 hu.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  have hLC : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := adMat_mul_eq_one (yx h hJ hW)
  refine sub_eq_zero.1 (eq_zero_of_mem_span_cols hLC h1 ?_)
  rintro i ⟨k, hk, hik, hkj⟩
  have hkT : k ∈ T := by
    rcases Finset.mem_insert.1 hk with rfl | hk'
    · exact absurd (hkj.trans hκj) (lt_irrefl _)
    · exact hk'
  have hl' := inv_mem hl
  simp only [levi, Subgroup.mem_iInf] at hl'
  obtain ⟨B, -, e⟩ := (Subgroup.mem_inf.1 (hl' k hkT)).2
  have h2 := mul_eq_of_conj (A := adMat F J) (sigR (AF F) σ) (mat_inv_mul g) (g⁻¹).2 e
  rw [cT_initCols_mul] at h2
  set L := (adMat F (cT (σ : E →+* E) Y * J)).submatrix (Fin.castLE k.2) id with hL
  have h3 : L *ᵥ (adMat F X)ᵀ j = 0 := by
    funext p
    have hp : Fin.castLE k.2 p ≠ j := fun hc => by
      have h4 : (Fin.castLE k.2 p).val ≤ k.val := Nat.le_of_lt_succ p.2
      have h5 : k.val < j.val := hkj
      rw [hc] at h4
      omega
    exact (congrFun (congrFun hLC (Fin.castLE k.2 p)) j).trans (Matrix.one_apply_ne hp)
  have h4 : L *ᵥ ((matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j) = 0 := by
    rw [mulVec_sub, mulVec_mulVec, h2, ← mulVec_mulVec, h3, mulVec_zero, sub_zero]
  exact congrFun h4 ⟨i.val, Nat.lt_succ_of_le hik⟩

theorem fix_y (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)} {κ : Fin r}
    (hκ : κ ∉ upTo T) {g : GAd σ J} (hl : g ∈ levi σ J X Y T) (hu : g ∈ unip σ J X (insert κ T)) {i : Fin r}
    (hi : i ∈ upTo T) : (matHom _ σ J g).1 *ᵥ (adMat F Y)ᵀ i = (adMat F Y)ᵀ i := by
  obtain ⟨k, hkT, hik⟩ := hi
  simp only [levi, Subgroup.mem_iInf] at hl
  obtain ⟨B, -, e⟩ := (Subgroup.mem_inf.1 (hl k hkT)).2
  have hGC : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) :=
    Matrix.ext_col fun p => exists_height_lower_bound h hJ hW hκ (by simpa only [levi, Subgroup.mem_iInf] using hl) hu
      ⟨k, hkT, Nat.le_of_lt_succ p.2⟩
  have hCD : cT (sigR (AF F) σ) (adMat F (initCols X k)) * adMat F J * adMat F (initCols Y k) = 1 := by
    rw [cT_initCols_mul]
    have h1 : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := adMat_mul_eq_one hW.xy
    exact Matrix.ext fun p q => (congrFun (congrFun h1 (Fin.castLE k.2 p)) (Fin.castLE k.2 q)).trans (by simp [Matrix.one_apply])
  have h2 := mul_eq_self_of_pair (A := adMat F J) (sigR (AF F) σ) g.2 hCD hGC e
  exact congrArg (fun M => Mᵀ ⟨i.val, Nat.lt_succ_of_le hik⟩) h2

theorem levi_inf_unip_le_uPart_general (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (T : Finset (Fin r)) {κ : Fin r} (hκ : κ ∉ upTo T) :
    levi σ J X Y T ⊓ unip σ J X (insert κ T) ≤ uPart σ J X Y T := by
  rintro g ⟨hl, hu⟩
  have key : colSpan F X (upTo T) ⊔ colSpan F Y (upTo T) ≤ LinearMap.eqLocus (matHom _ σ J g).1.mulVecLin LinearMap.id := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact exists_height_lower_bound h hJ hW hκ hl hu hj
    · rintro _ ⟨j, hj, rfl⟩
      exact fix_y h hJ hW hκ hl hu hj
  exact fun y hy => key hy

end Frame

theorem levi_inf_unip_le_uPart : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (κ : Fin m), κ ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → levi D.sp.cm.sig V.gram X Y T ⊓ unip D.sp.cm.sig V.gram X (insert κ T) ≤ uPart D.sp.cm.sig V.gram X Y T := by
  intro D V m X Y hW T κ hκ
  obtain ⟨h, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  exact levi_inf_unip_le_uPart_general h (hJ' V) hW T hκ

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedConstantTermCompatible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n n' : ℕ} (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) {m m' : ℕ}

theorem mulVec_col {R : Type} [CommRing R] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R)
    (i : Fin c) : A *ᵥ Bᵀ i = (A * B)ᵀ i := by
  ext j
  rfl


omit [NumberField E] in
variable {σ J} in
theorem mem_iff_of_ptStab {A A' : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {g : GAd σ J}
    (h : g ∈ ptStab σ J A) (hA : A' ≤ A) (y : Fin n → AF F ⊗[F] E) :
    y ∈ A' ↔ (matHom _ σ J g).1 *ᵥ y ∈ A' := by
  refine ⟨fun hy => by rwa [h y (hA hy)], fun hy => ?_⟩
  have h1 := (inv_mem h) _ (hA hy)
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at h1
  rwa [h1]


omit [NumberField E] in
variable {σ J J'} in
theorem mem_unip_of_mat {T : Finset (Fin m)} {X : Matrix (Fin n) (Fin m) E} {X' : Matrix (Fin n') (Fin m') E}
    {I : Matrix (Fin n) (Fin n') E} {P : Matrix (Fin n') (Fin n) E} {e : Fin m' → Fin m}
    (he : StrictMono e) (hr : ∀ i, i ∉ upTo T ↔ i ∈ Set.range e)
    (hIX : I * X' = X.submatrix id e) (hPX : P * X.submatrix id e = X')
    (hPT : ∀ l ∈ upTo T, ∀ i, (P * X) i l = 0)
    (hG : Formalism.UG.cT (σ : E →+* E) I * J = J' * P)
    {g : GAd σ J} {b : GAd σ J'}
    (hg : (matHom _ σ J g).1 = 1 + adMat F I * ((matHom _ σ J' b).1 - 1) * adMat F P)
    {k : Fin m'} (hb : b ∈ unip σ J' X' {k}) : g ∈ unip σ J X (insert (e k) T) := by
  classical
  have c0 : ∀ {a c d : ℕ} (U : Matrix (Fin a) (Fin c) E) (W : Matrix (Fin c) (Fin d) E),
      adMat F U * adMat F W = adMat F (U * W) := fun U W => (Matrix.map_mul ..).symm
  have dM : ∀ y, (matHom _ σ J g).1 *ᵥ y - y =
      adMat F I *ᵥ ((matHom _ σ J' b).1 *ᵥ (adMat F P *ᵥ y) - adMat F P *ᵥ y) := fun y => by
    rw [hg, add_mulVec, one_mulVec, add_sub_cancel_left, ← mulVec_mulVec, ← mulVec_mulVec, sub_mulVec, one_mulVec]
  have pe : ∀ i, adMat F P *ᵥ (adMat F X)ᵀ (e i) = (adMat F X')ᵀ i := fun i => by
    rw [mulVec_col, c0]
    conv_rhs => rw [← hPX]
    rfl
  have ie : ∀ i, adMat F I *ᵥ (adMat F X')ᵀ i = (adMat F X)ᵀ (e i) := fun i => by
    rw [mulVec_col, c0, hIX]
    rfl
  have hz : ∀ l ∈ upTo T, adMat F P *ᵥ (adMat F X)ᵀ l = 0 := fun l hl => by
    rw [mulVec_col, c0]
    ext i
    change inclR (F := F) (AF F) ((P * X) i l) = 0
    rw [hPT l hl i, map_zero]
  have ip : ∀ (S : Set (Fin m')) y, y ∈ colSpan F X' S → adMat F I *ᵥ y ∈ colSpan F X (e '' S) := fun S y hy => by
    refine (Submodule.span_le (p := (colSpan F X (e '' S)).comap (adMat F I).mulVecLin)).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    change adMat F I *ᵥ _ ∈ colSpan F X (e '' S)
    rw [ie]
    exact Submodule.subset_span ⟨e i, ⟨i, hi, rfl⟩, rfl⟩
  have e0 : {i | ∃ k' ∈ ({k} : Finset (Fin m')), i ≤ k'} = {i | i ≤ k} := by simp
  have fixB : ∀ i ≤ k, (matHom _ σ J' b).1 *ᵥ (adMat F X')ᵀ i = (adMat F X')ᵀ i := fun i hi => by
    have h := (Subgroup.mem_iInf.1 hb.1 i).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
    have e3 : {l | ∃ k' ∈ ({k} : Finset (Fin m')), l ≤ k' ∧ k' < i} = ∅ := by
      ext l
      simpa using fun _ => hi
    rw [e3, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  have spanB : ∀ j, k < j → (matHom _ σ J' b).1 *ᵥ (adMat F X')ᵀ j - (adMat F X')ᵀ j ∈ colSpan F X' {i | i ≤ k} :=
    fun j hj => by
      have h := (Subgroup.mem_iInf.1 hb.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
      have e2 : {l | ∃ k' ∈ ({k} : Finset (Fin m')), l ≤ k' ∧ k' < j} = {i | i ≤ k} := by simp [hj]
      rwa [e2] at h
  have perpB : ∀ w ∈ colPerp σ J' X' {i | i ≤ k}, (matHom _ σ J' b).1 *ᵥ w - w ∈ colSpan F X' {i | i ≤ k} := fun w hw => by
    have h := hb.2.2 w (by rwa [e0])
    rwa [e0] at h
  let A : Set (Fin m) := {i | ∃ k' ∈ insert (e k) T, i ≤ k'}
  have hup : ∀ i, i ∈ upTo T → i ∈ A := fun i ⟨t, ht, hi⟩ => ⟨t, Finset.mem_insert_of_mem ht, hi⟩
  have hA : ∀ i ∈ A, i ∈ upTo T ∨ ∃ i', i' ≤ k ∧ e i' = i := fun i ⟨t, ht, hi⟩ => by
    rcases Finset.mem_insert.1 ht with rfl | ht
    · by_cases h : i ∈ upTo T
      · exact Or.inl h
      · obtain ⟨i', rfl⟩ := (hr i).1 h
        exact Or.inr ⟨i', he.le_iff_le.1 hi, rfl⟩
    · exact Or.inl ⟨t, ht, hi⟩
  have fix : ∀ i ∈ A, (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i = (adMat F X)ᵀ i := fun i hi => by
    rw [← sub_eq_zero, dM]
    rcases hA i hi with h | ⟨i', h, rfl⟩
    · rw [hz i h, mulVec_zero, sub_zero, mulVec_zero]
    · rw [pe, fixB i' h, sub_self, mulVec_zero]
  have pt : g ∈ ptStab σ J (colSpan F X A) := fun y hy => by
    refine (Submodule.span_le (p := LinearMap.eqLocus (matHom _ σ J g).1.mulVecLin LinearMap.id)).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    exact fix i hi
  have pp : ∀ y ∈ colPerp σ J X A, adMat F P *ᵥ y ∈ colPerp σ J' X' {i | i ≤ k} := fun y hy => by
    simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
    intro i hi
    have h1 : Formalism.UG.cT (σ : E →+* E) X' * J' * P = (Formalism.UG.cT (σ : E →+* E) X * J).submatrix e id := by
      rw [Matrix.mul_assoc, ← hG, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hIX]
      rfl
    have h2 := hy (e i) ⟨e k, Finset.mem_insert_self _ _, he.monotone hi⟩
    change (adMat F (Formalism.UG.cT (σ : E →+* E) X' * J') *ᵥ adMat F P *ᵥ y) i = 0
    rw [mulVec_mulVec, c0, h1]
    exact h2
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨mem_iff_of_ptStab pt ?_, fun y hy => ?_⟩,
    mem_iff_of_ptStab pt le_rfl, fun y hy => ?_⟩
  · exact Submodule.span_mono (Set.image_mono fun i ⟨k', h1, h2, _⟩ => ⟨k', h1, h2⟩)
  · suffices h : y ∈ (colSpan F X {i | ∃ k' ∈ insert (e k) T, i ≤ k' ∧ k' < j}).comap
        ((matHom _ σ J g).1 - 1).mulVecLin by
      rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec] at h
    refine (Submodule.span_le (p := (colSpan F X {i | ∃ k' ∈ insert (e k) T, i ≤ k' ∧ k' < j}).comap
      ((matHom _ σ J g).1 - 1).mulVecLin)).2 ?_ hy
    rintro _ ⟨j, rfl, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec]
    by_cases hj : j ∈ A
    · rw [fix j hj, sub_self]
      exact zero_mem _
    · obtain ⟨j', rfl⟩ := (hr j).1 fun h => hj (hup j h)
      have hk : k < j' := lt_of_not_ge fun h => hj ⟨e k, Finset.mem_insert_self _ _, he.monotone h⟩
      rw [dM, pe]
      refine Submodule.span_mono (Set.image_mono ?_) (ip _ _ (spanB j' hk))
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨e k, Finset.mem_insert_self _ _, he.monotone hi, he hk⟩
  · rw [dM]
    refine Submodule.span_mono (Set.image_mono ?_) (ip _ _ (perpB _ (pp y hy)))
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨e k, Finset.mem_insert_self _ _, he.monotone hi⟩

end Core

theorem unip_embed : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b ∈ unip D.sp.cm.sig V'.gram X' {k}, s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) := by
  intro D V m X Y hW T V' ι hι hR m' e X' Y' hS hW' s hs k b hb
  obtain ⟨he, hr, hX, -⟩ := hS
  refine mem_unip_of_mat he hr hX ?_ ?_ cT_frameMat_mul_gram (mat_eq hι hs b) hb
  · rw [← hX, ← Matrix.mul_assoc, prM_mul_frameMat hι, Matrix.one_mul]
  · intro l hl i
    have h := prM_mulVec_eq_zero (V' := V') (ι := ι) (x := fun j => X j l) fun v' => ((hR (ι v')).1 ⟨v', rfl⟩ l hl).1
    exact congrFun h i

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
end

