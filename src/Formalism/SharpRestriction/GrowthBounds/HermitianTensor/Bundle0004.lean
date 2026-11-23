module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LastNeZero
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem last_ne_zero'' (m : ℕ) (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_last, Fin.val_zero] at this
  omega

theorem lamAt_add' {n' m : ℕ} (X Y : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (X + Y) s = lamAt X s + lamAt Y s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.add_apply]
    ring

theorem lamAt_sub' {n' m : ℕ} (X Y : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (X - Y) s = lamAt X s - lamAt Y s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.sub_apply]
    ring

theorem lamAt_dualW {n' m : ℕ} (lo : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (dualW lo) s = dualWt (lamAt lo s) := by
  unfold lamAt dualW
  split_ifs <;> rfl

theorem dualWt_anti {m : ℕ} (mu : Fin (m + 1) → ℤ) (h : Antitone mu) : Antitone (dualWt mu) := by
  intro i j hij
  simp only [dualWt]
  have := h (Fin.rev_le_rev.mpr hij)
  linarith

theorem flatW_top {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : TT) :
    flatW m al be s.val = wtPQ m (al s) (be s) := by
  funext i
  simp only [flatW, wtPQ, dif_pos s.2]

theorem flatW_off {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (hs : s ∉ TT) :
    flatW m al be s = 0 := by
  funext i
  simp only [flatW, dif_neg hs, Pi.zero_apply]

theorem flatW_add {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be al' be' : TT → ℕ) :
    flatW m (fun s => al s + al' s) (fun s => be s + be' s) = flatW m al be + flatW m al' be' := by
  funext s i
  simp only [flatW, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

theorem lo_apply (m : ℕ) (ccl P Q : ℕ) (lam : Fin (m + 1) → ℤ) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last m) = -((Q : ℤ) + ccl)) (i : Fin (m + 1)) :
    (lam - wtPQ m P Q) i = if i = 0 then (ccl : ℤ) else if i = Fin.last m then -(ccl : ℤ) else lam i := by
  simp only [Pi.sub_apply, wtPQ]
  split_ifs with h1 h2
  · subst h1
    rw [h0]
    ring
  · subst h2
    rw [hl]
    ring
  · ring

theorem bE_snd {K : Type} [Field K] {α : Type} (b : Bool) (f : MvPolynomial α K) :
    rename (Prod.snd : Bool × α → α) (rename (fun v => (b, v)) f) = f := by
  rw [rename_rename]
  exact congrArg (fun φ => φ f) rename_id

theorem posOK_zero {p n' : ℕ} (R : RS p n') (m : ℕ) : PosOK R m 0 0 0 0 0 0 1 0 := by
  haveI := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have hz := tn_nuOf_zero m

  let abelian₂ : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf :=
    (rename (Prod.snd : Bool × (Fin (m + 1) × Fin (m + 1)) → Fin (m + 1) × Fin (m + 1))).toLinearMap
  have hLam : ∀ v t : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
      abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) = v * t := by
    intro v t
    simp only [abelian₂, AlgHom.toLinearMap_apply, map_mul, blockEmb, bE_snd]
  have hlat : ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (c : R.Kf), IsUnit g.det → c ≠ 0 →
      IsLattice R.O (colSpan R.O (g * lb_D (m + 1) 1 c)) :=
    fun g c hg hc => ⟨_, by rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ c hc), rfl⟩
  have h1H : ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ →
      (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) ∈ H0 R.O m 0 Λ :=
    fun Λ hΛ => (invariant_sections_zero_weight_iff m Λ hΛ 1).mpr ⟨1, by simp⟩
  refine ⟨abelian₂, ?_, ?_, ?_⟩
  · intro v hv t ht
    rw [hLam]
    rw [hz] at hv ht ⊢
    rw [tn_const _ _ v hv, tn_const _ _ t ht, ← C_mul]
    exact tn_C_mem _ _ _
  · intro Λ hΛ v hv t ht
    rw [hLam]
    obtain ⟨a, rfl⟩ := (invariant_sections_zero_weight_iff m Λ hΛ v).mp hv
    obtain ⟨b, rfl⟩ := (invariant_sections_zero_weight_iff m Λ hΛ t).mp ht
    exact (invariant_sections_zero_weight_iff m Λ hΛ _).mpr ⟨a * b, by rw [map_mul, C_mul]⟩
  · intro g hg
    refine ⟨1, 1, fun _ => 1, fun _ => 1, fun _ => 0, by simp, fun _ => le_rfl, ?_, ?_⟩
    · intro a' b F _
      rw [hLam, Subsingleton.elim a' b]
      simp
    · intro c hc
      have hL := hlat g c hg hc
      simp only [Pi.zero_apply, zpow_zero, one_smul]
      refine ⟨h1H _ hL, ?_, fun _ => h1H _ hL, fun _ => h1H _ hL⟩
      rintro ⟨z', hz', he⟩
      obtain ⟨d, rfl⟩ := (invariant_sections_zero_weight_iff m _ hL z').mp hz'
      have h2 : (C (algebraMap R.O R.Kf 1) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) =
          C (algebraMap R.O R.Kf (R.w * d)) := by
        rw [map_one, map_one, map_mul, C_mul, tn_smulC]
        exact he
      have h3 := hinj (MvPolynomial.C_injective _ _ h2)
      exact R.std.2.1.not_isUnit (IsUnit.of_mul_eq_one _ h3.symm)

theorem posOK_top (h1 : CloudOne) {p n' : ℕ} (R : RS p n') (mm : ℕ) (hmm : 1 ≤ mm) (a ccl P Q : ℕ)
    (lam : Fin (mm + 1 + 1) → ℤ) (hlam : Antitone lam) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl))
    (hmid : ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) (h8 : 2 * ccl ≤ 8 * a) :
    PosOK R (mm + 1) lam (wtPQ (mm + 1) P Q) (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))
      (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) (lam - wtPQ (mm + 1) P Q) (dualWt (lam - wtPQ (mm + 1) P Q))
      (weylDim mm (fun j => lam j.castSucc.succ)) ⌈kappaOneExponent p a (mm + 1)⌉₊ := by
  obtain ⟨abelian₂, hA, hB, hC⟩ := h1 p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  refine ⟨abelian₂, hA, hB, fun g hg => ?_⟩
  obtain ⟨nb, z0, s, s', ka, e1, e2, e3, e4⟩ := hC g hg
  refine ⟨nb, z0, s, s', ka, e1, e2, e3, fun c hc => ?_⟩
  have hl0 := last_ne_zero'' (mm + 1) (by omega)
  have z1 : (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = ((2 * ccl : ℕ) : ℤ) := by simp [wtPQ]
  have z2 : (lam - wtPQ (mm + 1) P Q) 0 = ((ccl : ℕ) : ℤ) := by
    rw [lo_apply (mm + 1) ccl P Q lam h0 hl, if_pos rfl]
  have z3 : (dualWt (lam - wtPQ (mm + 1) P Q)) 0 = ((ccl : ℕ) : ℤ) := by
    simp only [dualWt, Fin.rev_zero]
    rw [lo_apply (mm + 1) ccl P Q lam h0 hl, if_neg hl0, if_pos rfl, neg_neg]
  rw [z1, z2, z3, zpow_natCast, zpow_natCast]
  exact e4 c hc

theorem top_hyps {n' mm : ℕ} (TT : Finset (Fin n')) (ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ) (hBase : IsBaseWeight TT aw bw ccl lam0)
    (hAB : ∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) (s : TT) :
    lam0 s.val 0 = (A s : ℤ) + ccl ∧ lam0 s.val (Fin.last (mm + 1)) = -((B s : ℤ) + ccl) ∧
      ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam0 s.val i| ≤ ccl := by
  obtain ⟨h0, hl, hm⟩ := (hBase s.val).1 s.2
  obtain ⟨hA, hB⟩ := hAB s
  exact ⟨by rw [h0]; linarith, by rw [hl]; linarith, hm⟩

theorem posOK_at_top (h1 : CloudOne) {p n' : ℕ} (R : RS p n') (mm : ℕ) (hmm : 1 ≤ mm) (TT : Finset (Fin n'))
    (a ccl : ℕ) (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ)
    (hBase : IsBaseWeight TT aw bw ccl lam0) (hDom : IsDominant lam0)
    (hAB : ∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) (h8 : 2 * ccl ≤ 8 * a) (s : TT) :
    PosOK R (mm + 1) (lamAt lam0 s.val) (lamAt (flatW (mm + 1) A B) s.val)
      (lamAt (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) s.val)
      (lamAt (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)) s.val)
      (lamAt (lam0 - flatW (mm + 1) A B) s.val) (lamAt (dualW (lam0 - flatW (mm + 1) A B)) s.val)
      (weylDim mm (cloudAt lam0 s.val)) ⌈kappaOneExponent p a (mm + 1)⌉₊ := by
  obtain ⟨t0, tl, tm⟩ := top_hyps TT ccl aw bw lam0 A B hBase hAB s
  have hl0 := last_ne_zero'' (mm + 1) (by omega)

  have hflat : ∀ al be : TT → ℕ, lamAt (flatW (mm + 1) al be) s.val =
      if Even s.val.val then wtPQ (mm + 1) (al s) (be s) else wtPQ (mm + 1) (be s) (al s) := by
    intro al be
    unfold lamAt
    split_ifs with he
    · exact flatW_top (mm + 1) al be s
    · funext i
      rw [flatW_top]
      simp only [wtPQ]
      by_cases hi0 : i = 0
      · subst hi0
        simp [Fin.rev_zero, hl0]
      · by_cases hil : i = Fin.last (mm + 1)
        · subst hil
          simp [Fin.rev_last, hl0]
        · have h1 : i.rev ≠ 0 := fun h => hil (by rw [← Fin.rev_rev i, h, Fin.rev_zero])
          have h2 : i.rev ≠ Fin.last (mm + 1) := fun h => hi0 (by rw [← Fin.rev_rev i, h, Fin.rev_last])
          simp [hi0, hil, h1, h2]
  rw [lamAt_sub', lamAt_dualW, lamAt_sub', hflat, hflat, hflat]
  rw [show cloudAt lam0 s.val = fun j => lamAt lam0 s.val j.castSucc.succ from rfl]
  by_cases he : Even s.val.val
  · simp only [if_pos he]
    have hlam' : lamAt lam0 s.val = lam0 s.val := by
      unfold lamAt
      rw [if_pos he]
    rw [hlam']
    exact posOK_top h1 R mm hmm a ccl (A s) (B s) (lam0 s.val) (hDom s.val) t0 tl tm h8
  · simp only [if_neg he]
    have hlam' : lamAt lam0 s.val = fun i => -lam0 s.val i.rev := by
      unfold lamAt
      rw [if_neg he]
    rw [hlam']
    refine posOK_top h1 R mm hmm a ccl (B s) (A s) _ (dualWt_anti _ (hDom s.val)) ?_ ?_ ?_ h8
    · simp only [Fin.rev_zero]
      rw [tl]
      try ring
    · simp only [Fin.rev_last]
      rw [t0]
      try ring
    · intro i hi1 hi2
      rw [abs_neg]
      refine tm i.rev ?_ ?_
      · rw [Fin.val_rev]
        omega
      · rw [Fin.val_rev]
        omega

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ProdMemHten
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

section Mul

variable {Kf : Type} [Field Kf] {n' m : ℕ}

theorem mulV_mem (X Y Z : Fin n' → Fin (m + 1) → ℤ) (hX : IsDominant X) (hY : IsDominant Y) (hZ : IsDominant Z)
    (h : ∀ s, lamAt Z s = lamAt X s + lamAt Y s) :
    ∀ F ∈ Vsp Kf X, ∀ r ∈ Vsp Kf Y, F * r ∈ Vsp Kf Z := by
  intro F hF r hr
  unfold Vsp at hF hr ⊢
  refine tensorLat_mul _ _ _ (fun s f hf g hg => ?_) F hF r hr
  simp only [if_pos (lamAt_anti X hX s)] at hf
  simp only [if_pos (lamAt_anti Y hY s)] at hg
  simp only [if_pos (lamAt_anti Z hZ s)]
  rw [h s, cbNuOf_add _ _ (lamAt_anti X hX s) (lamAt_anti Y hY s)]
  exact Formalism.GradedWeylDivisibility.dualWeyl_mul hf hg

def mulV (X Y Z : Fin n' → Fin (m + 1) → ℤ) (hX : IsDominant X) (hY : IsDominant Y) (hZ : IsDominant Z)
    (h : ∀ s, lamAt Z s = lamAt X s + lamAt Y s) : Vsp Kf X →ₗ[Kf] Vsp Kf Y →ₗ[Kf] Vsp Kf Z :=
  LinearMap.mk₂ Kf (fun F r => ⟨F.1 * r.1, mulV_mem X Y Z hX hY hZ h _ F.2 _ r.2⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _))
    (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

variable {O : Type} [CommRing O] [Algebra O Kf]

theorem prod_mem_Hten (X : Fin n' → Fin (m + 1) → ℤ) (gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (c : Kf)
    (hc : c ≠ 0) (f : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hf : ∀ s, (c ^ (lamAt X s 0)) • f s ∈ H0 O m (lamAt X s) (colSpan O (gs s * lb_D _ 1 c))) :
    (c ^ Ar 1 X) • ∏ s, blockEmb Kf s (f s) ∈ Hten O X (famD O gs c) := by
  have hX : c ^ Ar 1 X = ∏ s, c ^ lamAt X s 0 := by
    rw [Ar_one, Formalism.MainNotions.G.LatticeSystems.lb_zpow_sum c hc]
  rw [hX, ← prod_bE_smul (fun s => c ^ lamAt X s 0) f]
  unfold Hten tensorLat
  exact Submodule.subset_span ⟨fun s => c ^ lamAt X s 0 • f s, hf, rfl⟩

theorem prod_mem_Vsp (X : Fin n' → Fin (m + 1) → ℤ) (hX : IsDominant X)
    (gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hgs : ∀ s, IsUnit (gs s).det)
    (f : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hf : ∀ s, ((1 : Kf) ^ (lamAt X s 0)) • f s ∈ H0 O m (lamAt X s) (colSpan O (gs s * lb_D _ 1 1))) :
    ∏ s, blockEmb Kf s (f s) ∈ Vsp Kf X := by
  have hL : ∀ s, IsLattice O (colSpan O (gs s * lb_D _ 1 (1 : Kf))) :=
    fun s => famD_lat O gs hgs 1 one_ne_zero s
  refine tn_Hten_le X hX (fun s => colSpan O (gs s * lb_D _ 1 (1 : Kf))) hL _ ?_
  unfold Hten tensorLat
  refine Submodule.subset_span ⟨f, fun s => ?_, rfl⟩
  simpa only [one_zpow, one_smul] using hf s

end Mul

theorem cloudTen {p n' : ℕ} (R : RS p n') (m : ℕ) (lam0 H Hp ze lo lo' : Fin n' → Fin (m + 1) → ℤ)
    (dlam : IsDominant lam0) (dH : IsDominant H) (dHp : IsDominant Hp) (dze : IsDominant ze) (dlo : IsDominant lo)
    (dlo' : IsDominant lo') (hadd1 : ∀ s, lamAt Hp s = lamAt H s + lamAt ze s)
    (hadd2 : ∀ s, lamAt lam0 s = lamAt H s + lamAt lo s) (d : Fin n' → ℚ) (κ : Fin n' → ℕ)
    (hpos : ∀ s, PosOK R m (lamAt lam0 s) (lamAt H s) (lamAt Hp s) (lamAt ze s) (lamAt lo s) (lamAt lo' s) (d s) (κ s))
    (hCO : CartanOnto) (hIso : CloudIsoP) :
    ∃ (mH : Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf ze →ₗ[R.Kf] Vsp R.Kf Hp)
      (mU : Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf lo →ₗ[R.Kf] Vsp R.Kf lam0)
      (abelian₂ : Vsp R.Kf lam0 →ₗ[R.Kf] Vsp R.Kf lo' →ₗ[R.Kf] Vsp R.Kf Hp),
      (∀ M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf), (∀ s, IsLattice R.O (M s)) →
        (∀ F ∈ toV H (Hten R.O H M), ∀ z ∈ toV ze (Hten R.O ze M), mH F z ∈ toV Hp (Hten R.O Hp M)) ∧
        (∀ F ∈ toV H (Hten R.O H M), ∀ z ∈ toV lo (Hten R.O lo M), mU F z ∈ toV lam0 (Hten R.O lam0 M)) ∧
        (∀ v ∈ toV lam0 (Hten R.O lam0 M), ∀ z ∈ toV lo' (Hten R.O lo' M), abelian₂ v z ∈ toV Hp (Hten R.O Hp M))) ∧
      ∀ gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf, (∀ s, IsUnit (gs s).det) →
        ∃ (nb : ℕ) (z0 : Vsp R.Kf ze) (s : Fin nb → Vsp R.Kf lo) (s' : Fin nb → Vsp R.Kf lo') (ka : Fin nb → ℕ),
          (nb : ℚ) = ∏ s, d s ∧ (∀ b, ka b ≤ ∑ s, κ s) ∧
          (∀ a' b F, abelian₂ (mU F (s b)) (s' a') = if a' = b then ((p : R.Kf) ^ ka b) • mH F z0 else 0) ∧
          ∀ c : R.Kf, c ≠ 0 →
            (c ^ Ar 1 ze) • z0 ∈ toV ze (Hten R.O ze (famD R.O gs c)) ∧
            (∀ b, (c ^ Ar 1 lo) • s b ∈ toV lo (Hten R.O lo (famD R.O gs c))) ∧
            (∀ a', (c ^ Ar 1 lo') • s' a' ∈ toV lo' (Hten R.O lo' (famD R.O gs c))) ∧
            (∀ F, mH F ((c ^ Ar 1 ze) • z0) ∈ toV Hp (Hten R.O Hp (famD R.O gs c)) →
              F ∈ toV H (Hten R.O H (famD R.O gs c))) := by
  classical
  haveI : IsFractionRing R.O R.Kf := R.std.1.frac_O
  have hw : Irreducible R.w := R.std.2.1
  have hH0 : ∀ (a b : Fin (m + 1) → ℤ), Antitone a → Antitone b →
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ →
        ∀ F ∈ H0 R.O m a Λ, ∀ G ∈ H0 R.O m b Λ, F * G ∈ H0 R.O m (a + b) Λ := by
    intro a b ha hb Λ hΛ F hF G hG
    rw [hCO R.O R.Kf m a b Λ hΛ ha hb]
    exact Submodule.subset_span ⟨F, hF, G, hG, rfl⟩
  unfold PosOK at hpos
  choose Ls hA hB hC using hpos
  obtain ⟨T, hT⟩ := KP.tensorMap (K := R.Kf) (S := Fin n')
    (fun s => (blockEmb R.Kf s).toLinearMap ∘ₗ Ls s)
  have hT' : ∀ Q : Fin n' → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf,
      T (∏ s, rename (fun x => (s, x)) (Q s)) = ∏ s, blockEmb R.Kf s (Ls s (Q s)) := fun Q => hT Q
  have hLV : ∀ V ∈ Vsp R.Kf lam0, ∀ W ∈ Vsp R.Kf lo', lamPoly T V W ∈ Vsp R.Kf Hp := by
    unfold Vsp
    refine lamPoly_mem T Ls hT' _ _ _ (fun s v hv t ht => ?_)
    simp only [if_pos (lamAt_anti lam0 dlam s)] at hv
    simp only [if_pos (lamAt_anti lo' dlo' s)] at ht
    simp only [if_pos (lamAt_anti Hp dHp s)]
    exact hA s v hv t ht
  refine ⟨mulV H ze Hp dH dze dHp hadd1, mulV H lo lam0 dH dlo dlam hadd2,
    LinearMap.mk₂ R.Kf (fun V W => (⟨lamPoly T V.1 W.1, hLV _ V.2 _ W.2⟩ : Vsp R.Kf Hp))
      (fun a b c => Subtype.ext (lamPoly_add_left T _ _ _))
      (fun c a b => Subtype.ext (lamPoly_smul_left T c _ _))
      (fun a b c => Subtype.ext (lamPoly_add_right T _ _ _))
      (fun c a b => Subtype.ext (lamPoly_smul_right T c _ _)), ?_, ?_⟩
  · intro M hM
    refine ⟨fun F hF z hz => ?_, fun F hF z hz => ?_, fun v hv z hz => ?_⟩
    · have hF' : F.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt H s) (M s)) := hF
      have hz' : z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt ze s) (M s)) := hz
      show F.1 * z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt Hp s) (M s))
      refine tensorLat_mul _ _ _ (fun s f hf g hg => ?_) _ hF' _ hz'
      rw [hadd1 s]
      exact hH0 _ _ (lamAt_anti H dH s) (lamAt_anti ze dze s) (M s) (hM s) f hf g hg
    · have hF' : F.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt H s) (M s)) := hF
      have hz' : z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt lo s) (M s)) := hz
      show F.1 * z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt lam0 s) (M s))
      refine tensorLat_mul _ _ _ (fun s f hf g hg => ?_) _ hF' _ hz'
      rw [hadd2 s]
      exact hH0 _ _ (lamAt_anti H dH s) (lamAt_anti lo dlo s) (M s) (hM s) f hf g hg
    · have hv' : v.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt lam0 s) (M s)) := hv
      have hz' : z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt lo' s) (M s)) := hz
      show lamPoly T v.1 z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt Hp s) (M s))
      exact lamPoly_mem T Ls hT' _ _ _ (fun s v' hv'' t ht => hB s (M s) (hM s) v' hv'' t ht) _ hv' _ hz'
  · intro gs hgs
    choose nb z0 sv sv' ka hnb hka hmul hcc using fun s => hC s (gs s) (hgs s)
    let e : Fin (∏ s, nb s) ≃ ((s : Fin n') → Fin (nb s)) := finPiFinEquiv.symm
    have key : ∀ f ∈ Vsp R.Kf H, ∀ a' b : Fin (∏ s, nb s),
        lamPoly T (f * ∏ s, blockEmb R.Kf s (sv s (e b s))) (∏ s, blockEmb R.Kf s (sv' s (e a' s))) =
          if a' = b then ((p : R.Kf) ^ (∑ s, ka s (e b s))) • (f * ∏ s, blockEmb R.Kf s (z0 s)) else 0 := by
      intro f hf a' b
      unfold Vsp tensorLat at hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨G, hG, rfl⟩ := hx
        have hGs : ∀ s, G s ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt H s)) := fun s => by
          have h := hG s
          simp only [if_pos (lamAt_anti H dH s)] at h
          exact h
        rw [show (∏ s, blockEmb R.Kf s (G s)) * ∏ s, blockEmb R.Kf s (sv s (e b s)) =
            ∏ s, blockEmb R.Kf s (G s * sv s (e b s)) by
          rw [← Finset.prod_mul_distrib]; simp only [map_mul]]
        rw [lamPoly_prod T Ls hT']
        by_cases hab : a' = b
        · subst hab
          have hfac : ∀ s, Ls s (blockEmb R.Kf true (G s * sv s (e a' s)) * blockEmb R.Kf false (sv' s (e a' s))) =
              ((p : R.Kf) ^ ka s (e a' s)) • (z0 s * G s) := fun s => by
            rw [hmul s _ _ _ (hGs s), if_pos rfl]
          rw [if_pos rfl]
          simp only [hfac]
          rw [prod_bE_smul, Finset.prod_pow_eq_pow_sum]
          congr 1
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun s _ => by rw [map_mul, mul_comm]
        · rw [if_neg hab]
          have hex : ∃ s, e a' s ≠ e b s := by
            by_contra hcon
            push_neg at hcon
            exact hab (e.injective (funext hcon))
          obtain ⟨s0, hs0⟩ := hex
          apply Finset.prod_eq_zero (Finset.mem_univ s0)
          rw [hmul s0 _ _ _ (hGs s0), if_neg hs0, map_zero]
      | zero => simp only [zero_mul, lamPoly_zero_left, smul_zero, ite_self]
      | add x y _ _ hx hy =>
        rw [add_mul, lamPoly_add_left, hx, hy]
        split_ifs
        · rw [add_mul, smul_add]
        · rw [add_zero]
      | smul c x _ hx =>
        rw [smul_mul_assoc, lamPoly_smul_left, hx]
        split_ifs
        · rw [smul_mul_assoc, smul_comm]
        · rw [smul_zero]
    refine ⟨∏ s, nb s,
      ⟨∏ s, blockEmb R.Kf s (z0 s), prod_mem_Vsp ze dze gs hgs z0 (fun s => (hcc s 1 one_ne_zero).1)⟩,
      fun b => ⟨∏ s, blockEmb R.Kf s (sv s (e b s)),
        prod_mem_Vsp lo dlo gs hgs _ (fun s => (hcc s 1 one_ne_zero).2.2.1 (e b s))⟩,
      fun a' => ⟨∏ s, blockEmb R.Kf s (sv' s (e a' s)),
        prod_mem_Vsp lo' dlo' gs hgs _ (fun s => (hcc s 1 one_ne_zero).2.2.2 (e a' s))⟩,
      fun b => ∑ s, ka s (e b s), ?_, ?_, ?_, ?_⟩
    · rw [Nat.cast_prod]
      exact Finset.prod_congr rfl fun s _ => hnb s
    · intro b
      exact Finset.sum_le_sum fun s _ => hka s _
    · intro a' b F
      obtain ⟨f, hf⟩ := F
      have hk := key f hf a' b
      split_ifs at hk ⊢ with hab
      · exact Subtype.ext hk
      · exact Subtype.ext hk
    · intro c hc
      refine ⟨?_, fun b => ?_, fun a' => ?_, fun F hF => ?_⟩
      · show (c ^ Ar 1 ze) • (∏ s, blockEmb R.Kf s (z0 s)) ∈ Hten R.O ze (famD R.O gs c)
        exact prod_mem_Hten ze gs c hc z0 (fun s => (hcc s c hc).1)
      · show (c ^ Ar 1 lo) • (∏ s, blockEmb R.Kf s (sv s (e b s))) ∈ Hten R.O lo (famD R.O gs c)
        exact prod_mem_Hten lo gs c hc _ (fun s => (hcc s c hc).2.2.1 (e b s))
      · show (c ^ Ar 1 lo') • (∏ s, blockEmb R.Kf s (sv' s (e a' s))) ∈ Hten R.O lo' (famD R.O gs c)
        exact prod_mem_Hten lo' gs c hc _ (fun s => (hcc s c hc).2.2.2 (e a' s))
      · show F.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt H s) (famD R.O gs c s))
        have hF' : F.1 * ((c ^ Ar 1 ze) • ∏ s, blockEmb R.Kf s (z0 s)) ∈
            tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt Hp s) (famD R.O gs c s)) := hF
        rw [Ar_one, ← Formalism.MainNotions.G.LatticeSystems.lb_zpow_sum c hc, ← prod_bE_smul, mul_comm] at hF'
        simp only [hadd1] at hF'
        have h2 : F.1 ∈ tensorLat R.Kf R.Kf
            (fun s => if Antitone (lamAt H s) then dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt H s)) else ⊥) := F.2
        have hfun : (fun s => if Antitone (lamAt H s) then dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt H s)) else ⊥) =
            fun s => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt H s)) :=
          funext fun s => if_pos (lamAt_anti H dH s)
        rw [hfun] at h2
        exact hIso R.O R.Kf R.w hw n' m (fun s => lamAt H s) (fun s => lamAt ze s) (lamAt_anti H dH)
          (lamAt_anti ze dze) (famD R.O gs c) (fun s => famD_lat R.O gs hgs c hc s)
          (fun s => c ^ lamAt ze s 0 • z0 s) (fun s => (hcc s c hc).1) (fun s => (hcc s c hc).2.1) F.1 h2 hF'

end Formalism.MainNotions.flipOneThree.Pf

end
end

