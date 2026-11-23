module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DvdOfCompl
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideCounting

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model

section Gen

variable {S : Type} [Fintype S] [DecidableEq S]

theorem tr_bA_emb (K : Type) [CommRing K] {k n : ℕ} (g : S → Matrix (Fin k) (Fin k) K) (s : S)
    (F : MvPolynomial (Fin k × Fin n) K) : blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) :=
  (blockActTensor K K S k n g).1 s F

theorem tr_prod_smul (K : Type) [CommRing K] {k n : ℕ} (c : S → K) (F : S → MvPolynomial (Fin k × Fin n) K) :
    (∏ s, c s) • ∏ s, blockEmb K s (F s) = ∏ s, blockEmb K s (c s • F s) := by
  rw [smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_smul, smul_eq_C_mul]

theorem tr_map_emb {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {k n : ℕ} (s : S)
    (P : MvPolynomial (Fin k × Fin n) R) : map f (blockEmb R s P) = blockEmb R' s (map f P) := by
  unfold blockEmb
  exact map_rename f _ P

theorem map_letter_substitution {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (m : ℕ) (vec : S → Bool)
    (P : MvPolynomial (S × Fin (m + 1)) R) : map f (Th0 R m vec P) = Th0 R' m vec (map f P) := by
  have key : (map f).comp (Th0 R m vec).toRingHom = (Th0 R' m vec).toRingHom.comp (map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Th0]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, Th0, aeval_X]
      rw [tr_map_emb, map_Nv]
  exact RingHom.congr_fun key P

theorem tr_rowAct_inv (K : Type) [Field K] {k n : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det)
    (x : MvPolynomial (Fin k × Fin n) K) : rowAct K g (rowAct K g⁻¹ x) = x := by
  have := congrArg (fun f => f x) (rowActMul K k n g g⁻¹)
  simp only [AlgHom.comp_apply] at this
  rw [this, Matrix.nonsing_inv_mul g hg, fl_rowAct_one]

theorem tr_multi_twist (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hM : ∀ s, IsUnit (M s).det)
    (G : MvPolynomial (S × Fin (m + 1)) K) (hG : G ∈ Pol K (m + 1) d) :
    (∏ s, (M s).det ^ (letterWt m (d s) (vec s) (Fin.last m))) • blockAct K M (Th0 K m vec G) =
      Th0 K m vec (Lin (fun s => Aa (vec s) (M s)) G) := by
  unfold Formalism.MainNotions.G.Pol at hG
  rw [restrictSupport_eq_span] at hG
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, rfl⟩ := hx
    beta_reduce
    rw [mono_factor, map_prod, map_prod, map_prod, map_prod]
    simp only [Th0_emb, Lin_emb, tr_bA_emb]
    rw [tr_prod_smul]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [twist_theta K m hm (d s) (vec s) (M s) (hM s) _ (partS_Hd K d μ hμ s)]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | smul a x _ hx => simp only [map_smul]; rw [smul_comm, hx]

theorem tr_tens_int (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hy : y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s))) :
    ∃ R : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) O,
      (∏ s, (M s).det ^ (lam s (Fin.last m))) • blockAct Kf M y = map (algebraMap O Kf) R := by
  unfold tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have h1 := fun s => (nablaLTwMem O Kf m (lam s) (M s) (hM s) (F s)).1 (hF s)
    choose G _ hG2 using h1
    refine ⟨∏ s, blockEmb O s (G s), ?_⟩
    rw [map_prod, map_prod]
    simp only [tr_bA_emb]
    rw [tr_prod_smul]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [tr_map_emb, ← hG2 s]
    rfl
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨R1, h1⟩ := hx
    obtain ⟨R2, h2⟩ := hy
    exact ⟨R1 + R2, by rw [map_add (f := _), smul_add, h1, h2, map_add (f := _)]⟩
  | smul a x _ hx =>
    obtain ⟨R1, h1⟩ := hx
    refine ⟨a • R1, ?_⟩
    rw [fl_map_smul, ← h1, ← algebraMap_smul Kf a x, map_smul, smul_comm, algebraMap_smul]

theorem tr_tens_lift (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (sO : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) O)
    (h : sO ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lam s)))) :
    ∃ y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s)),
      (∏ s, (M s).det ^ (lam s (Fin.last m))) • blockAct Kf M y = map (algebraMap O Kf) sO := by
  unfold tensorLat at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    have key : ∀ s, (M s).det ^ (lam s (Fin.last m)) • rowAct Kf (M s)
        (((M s).det ^ (lam s (Fin.last m)))⁻¹ • rowAct Kf (M s)⁻¹ (map (algebraMap O Kf) (G s))) =
        map (algebraMap O Kf) (G s) := by
      intro s
      rw [map_smul, smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ (hM s).ne_zero), one_smul, tr_rowAct_inv _ _ (hM s)]
    refine ⟨∏ s, blockEmb Kf s (((M s).det ^ (lam s (Fin.last m)))⁻¹ •
      rowAct Kf (M s)⁻¹ (map (algebraMap O Kf) (G s))), ?_, ?_⟩
    · apply Submodule.subset_span
      refine ⟨_, fun s => ?_, rfl⟩
      rw [nablaLTwMem O Kf m (lam s) (M s) (hM s), key s]
      exact ⟨G s, hG s, rfl⟩
    · rw [map_prod, map_prod]
      simp only [tr_bA_emb]
      rw [tr_prod_smul]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [tr_map_emb, key s]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y1, m1, h1⟩ := hx
    obtain ⟨y2, m2, h2⟩ := hy
    exact ⟨y1 + y2, Submodule.add_mem _ m1 m2, by rw [map_add (f := _), smul_add, h1, h2, map_add (f := _)]⟩
  | smul a x _ hx =>
    obtain ⟨y1, m1, h1⟩ := hx
    refine ⟨a • y1, Submodule.smul_mem _ _ m1, ?_⟩
    rw [fl_map_smul, ← h1, ← algebraMap_smul Kf a y1, map_smul, smul_comm, algebraMap_smul]

theorem tr_tens_le (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hy : y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s))) :
    y ∈ tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lam s))) := by
  unfold tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    obtain ⟨x, hx, hxF⟩ := hF s
    rw [← hxF]
    exact Submodule.smul_mem _ _ (nablaLLe O Kf (m + 1) (m + 1) _ (M s) (hM s) x hx)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul Kf a x]
    exact Submodule.smul_mem _ _ hx

end Gen

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestrictedWeightFirstTwoEq
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)

theorem map_thAll {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n' m : ℕ) (vec : Fin n' → Bool)
    (P : MvPolynomial (Fin n' × Fin (m + 1)) R) :
    map f (thAll R n' m vec P) = thAll R' n' m vec (map f P) := by
  have hN : ∀ (b : Bool) (c : Fin (m + 1)),
      map f (Formalism.L2.G.Model.Nv R m b c) = Formalism.L2.G.Model.Nv R' m b c := by
    intro b c
    cases b
    · simp only [Formalism.L2.G.Model.Nv, Bool.false_eq_true, if_false]
      have hg : Formalism.L2.G.Model.genM R' m =
          (map f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R →+* _).mapMatrix (Formalism.L2.G.Model.genM R m) := by
        ext a u
        simp [Formalism.L2.G.Model.genM]
      rw [hg, ← RingHom.map_adjugate]
      rfl
    · simp [Formalism.L2.G.Model.Nv]
  have key : (map f).comp (thAll R n' m vec).toRingHom = (thAll R' n' m vec).toRingHom.comp (map f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [thAll]
    · intro v
      simp [thAll, blockEmb, map_rename, hN]
  exact RingHom.congr_fun key P

theorem restricted_weight_first_two_eq {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (s : Fin n') (hs : s ∈ TT) : restW TT lam0 s 0 = restW TT lam0 s 1 := by
  have hle : lam0 s 1 ≤ lam0 s 0 := hdom s (Fin.zero_le _)
  have h10 : (1 : Fin (m + 1)) ≠ 0 := by
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  have ht := Int.toNat_of_nonneg (sub_nonneg.mpr hle)
  simp only [restW, flW, dT, flatDeg, hs, if_true, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h10]
  omega

theorem nu_odd {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (s : Fin n') (hs : s ∈ TT) (hv : vecE n' s = false) (t : Fin (m + 1)) (ht : m ≤ t.val + 1) :
    nuOf (lamAt (restW TT lam0) s) t = 0 := by
  have hodd : ¬ Even (s : ℕ) := by simpa [vecE] using hv
  have htl := t.isLt
  have hr : restW TT lam0 s t.rev = restW TT lam0 s 0 := by
    have hv' : t.rev.val ≤ 1 := by
      rw [Fin.val_rev]
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv' with h | h
    · have e : t.rev = 0 := Fin.ext (by rw [h, Fin.val_zero])
      rw [e]
    · have e : t.rev = 1 := by
        apply Fin.ext
        rw [h, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [e, restricted_weight_first_two_eq hm TT lam0 hdom s hs]
  simp only [nuOf, lamAt, hodd, if_false, Fin.rev_last, hr]
  simp

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstDtop
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders MvPolynomial

def pmat (R : Type) [CommRing R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (TV n' k) R) :=
  Matrix.of fun l i : Fin r => X (A l, Fin.castLE hrk i) ^ P l

theorem pmat_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {n' r k : ℕ} (hrk : r ≤ k)
    (A : Fin r → Fin n') (P : Fin r → ℕ) : map f (pmat R hrk A P).det = (pmat R' hrk A P).det := by
  rw [RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun l i => ?_)
  simp [pmat]

theorem pmat_ne (R : Type) [CommRing R] [Nontrivial R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n')
    (P : Fin r → ℕ) (hA : Function.Injective A) (hP : ∀ l, P l ≠ 0) : (pmat R hrk A P).det ≠ 0 := by
  classical
  intro h
  let x : TV n' k → R := fun v => if ∃ l : Fin r, A l = v.1 ∧ Fin.castLE hrk l = v.2 then 1 else 0
  have hev : (MvPolynomial.eval x).mapMatrix (pmat R hrk A P) = 1 := by
    ext l i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, pmat, Matrix.of_apply, map_pow, eval_X,
      Matrix.one_apply]
    by_cases hli : l = i
    · subst hli
      have hx : x (A l, Fin.castLE hrk l) = 1 := by
        simp only [x]
        rw [if_pos ⟨l, rfl, rfl⟩]
      rw [hx, one_pow, if_pos rfl]
    · have hx : x (A l, Fin.castLE hrk i) = 0 := by
        simp only [x]
        rw [if_neg]
        rintro ⟨l', h1, h2⟩
        apply hli
        have e1 : l' = l := hA h1
        have e2 : l' = i := Fin.ext (by simpa using congrArg Fin.val h2)
        rw [← e1, e2]
      rw [hx, zero_pow (hP l), if_neg hli]
  have h2 := congrArg (MvPolynomial.eval x) h
  rw [RingHom.map_det, hev, Matrix.det_one, map_zero] at h2
  exact one_ne_zero h2

section Fac

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  {r k : ℕ}

theorem Ifirst_emb (hrk : r ≤ k) (i : Fin r) :
    (Ifirst r k).orderEmbOfFin (first_columns_card hrk) i = Fin.castLE hrk i := by
  have hmono : StrictMono (Fin.castLE hrk) := by
    intro a b hab
    rw [Fin.lt_def] at hab ⊢
    simpa using hab
  have h := Finset.orderEmbOfFin_unique (first_columns_card hrk) (f := Fin.castLE hrk)
    (fun x => by simp [Ifirst]) hmono
  exact (congrFun h i).symm

theorem subst_Del (w : O) (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n') (hrk : r ≤ k)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (j : ℤ) :
    subst p n' O w n' r g (Del p n' O F g j) = map (algebraMap O (KK O))
      (pmat O hrk (fun l => posOf n' (F.fr j l.val)) (fun l => p ^ (zF F j - F.fr j l.val).toNat)).det := by
  have hIc := first_columns_card (k := k) hrk
  simp only [Del, minorI, dif_pos hIc, Ifirst_emb hrk]
  rw [AlgHom.map_det, RingHom.map_det]
  congr 1
  ext l i
  have hE := (hV.2.2.2.2.1 j l.val l.2).2
  have hnn : ¬ IsNormal r ((posOf n' (F.fr j l.val), Fin.castLE hrk i) : TV n' k) := by
    simp only [IsNormal]
    rw [if_pos ((posOf_even hn _).mpr hE)]
    simp only [Fin.coe_castLE, not_le]
    exact i.2
  simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, twRow, pmat,
    map_pow, subst_xg w r hg hn _ hE, newVar, if_neg hnn, map_X]

theorem subst_Dtop' (w : O) (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r)
    (hrk : r ≤ k) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (s : ℤ) :
    subst p n' O w n' r g (Dtop p n' O F hrk g s) = map (algebraMap O (KK O))
      (pmat O hrk (fun l => posOf n' (Arow F s l.val)) (fun l => p ^ (s - Arow F s l.val).toNat)).det := by
  have hok : RowsEvenTopsBefore F s := by
    intro l hl
    rw [symbolGeneratorData.dv_Arow_get hV hn hr s l hl]
    generalize_proofs hp
    have hm := List.getElem_mem hp
    simp only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico] at hm
    exact ⟨hm.2.2, hm.2.1, hm.1.2⟩
  rw [subst_top_determinant w F hrk hg hn s hok]
  rfl

end Fac

end Formalism.MainNotions.TestSideCounting
end
end

