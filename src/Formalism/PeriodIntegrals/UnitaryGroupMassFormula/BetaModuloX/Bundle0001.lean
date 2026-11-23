module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.Skeleton
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.WAniso

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.LatticeSubOrthogonalHolds
section
noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.BetaModX

section Loc

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module (𝓞 E) V]

theorem le_locP (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) V) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L := by
  intro x hx
  show ∃ s ∈ p.primeCompl, s • x ∈ L
  exact ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hx⟩

theorem localization_mono (p : Ideal (𝓞 E)) [p.IsPrime] {L L' : Submodule (𝓞 E) V} (h : L ≤ L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ p.primeCompl, s • x ∈ L := hx
  show ∃ s ∈ p.primeCompl, s • x ∈ L'
  exact ⟨s, hs, h hsx⟩

theorem mem_localization_of_smul_mem' (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) V) (x : V) (s : 𝓞 E) (hs : s ∉ p)
    (h : s • x ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L := by
  obtain ⟨t, ht, htx⟩ : ∃ t ∈ p.primeCompl, t • s • x ∈ L := h
  have hs' : s ∈ p.primeCompl := hs
  show ∃ s ∈ p.primeCompl, s • x ∈ L
  exact ⟨t * s, p.primeCompl.mul_mem ht hs', by rw [mul_smul]; exact htx⟩

theorem mem_of_locP (N : Submodule (𝓞 E) V) (x : V)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N)) : x ∈ N := by

  let I : Ideal (𝓞 E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) V x) N
  have hmem : ∀ r : 𝓞 E, r ∈ I ↔ r • x ∈ N := fun r => by
    show (LinearMap.toSpanSingleton (𝓞 E) V x) r ∈ N ↔ r • x ∈ N
    rw [LinearMap.toSpanSingleton_apply]
  by_contra hx
  have hIt : I ≠ ⊤ := by
    intro hI
    apply hx
    have h1 : (1 : 𝓞 E) ∈ I := by rw [hI]; exact Submodule.mem_top
    have h2 := (hmem 1).1 h1
    rwa [one_smul] at h2
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hIt
  have hMb : M ≠ ⊥ := by
    intro hb
    rw [hb] at hM
    exact NumberField.RingOfIntegers.not_isField E (Ring.isField_iff_maximal_bot.mpr hM)
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ M.primeCompl, s • x ∈ N :=
    h ⟨M, hM.isPrime, hMb⟩
  exact hs (hIM ((hmem s).2 hsx))

end Loc

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lattice_sub_orthogonal_holds : XLamSub := by
  intro D u u' F0 Λ hΛ y x hx
  obtain ⟨-, ⟨-, -, -, hlc⟩, -⟩ := hΛ
  obtain ⟨-, ⟨ξ, hξl, hξd, hξm⟩, hyc, -⟩ := y.2
  have hxΛ : x ∈ Λ := (Submodule.mem_inf.1 hx).1
  refine mem_of_locP _ x (fun P => ?_)
  haveI := P.isPrime
  by_cases hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  swap
  · apply mem_localization_of_smul_mem' P.asIdeal _ x ((gS D : ℕ) : 𝓞 D.host.E) hgP
    apply le_locP
    exact Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hxΛ)

  have hsm : ∀ (o : 𝓞 D.host.E) (v : (VS D).V), v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) → ((o : D.host.E)) • v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
    intro o v hv
    have h1 := (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1)).smul_mem o hv
    rwa [← algebraMap_smul D.host.E o v] at h1

  have hye : ∀ b, y.1.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
    intro b
    obtain ⟨cy, -, hcy1, hcyeq⟩ := hyc.1 P
    have hmem : cy b • y.1.fl.e b ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => cy a • y.1.fl.e a) :=
      Submodule.subset_span ⟨b, rfl⟩
    rw [hcy1 hgP b, one_smul] at hmem
    have h1 : y.1.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ y.1) := by
      rw [hcyeq]
      exact le_locP _ _ hmem
    exact localization_mono P.asIdeal le_sup_right h1

  have key : ∀ n : ℕ, ∀ b : Fin D.R.rS, (b : ℕ) = n → (lf D F0).fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih b hbn
    have hm := hξm (Fin.castSucc b)
    unfold ModG frameAct frame at hm
    have hdiff := localization_mono P.asIdeal (le_sup_left : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) (hm P hgP)
    have hY : y.1.fl.fvec (Fin.castSucc b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
      simpa [Formalism.MainNotions.S.FlagG.fvec] using hye b
    have hS : (∑ a, ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
      have h1 := Submodule.sub_mem _ hY hdiff
      rwa [sub_sub_cancel] at h1
    have hR : (∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
      refine Submodule.sum_mem _ (fun a ha => ?_)
      have hab : a ≠ Fin.castSucc b := Finset.ne_of_mem_erase ha
      rcases lt_or_gt_of_ne hab with h | h
      · obtain ⟨a', rfl⟩ : ∃ a' : Fin D.R.rS, Fin.castSucc a' = a := ⟨⟨a.val, lt_trans h b.isLt⟩, Fin.ext rfl⟩
        have h' : (a' : ℕ) < (b : ℕ) := h
        simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
        exact hsm _ _ (ih a' (by omega) a' rfl)
      · rw [hξl a (Fin.castSucc b) h]
        simp
    have hsum := Finset.add_sum_erase Finset.univ (fun a => ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) (Finset.mem_univ (Fin.castSucc b))
    have h2 : ((ξ (Fin.castSucc b) (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec (Fin.castSucc b) =
        (∑ a, ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) -
          ∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a :=
      eq_sub_of_add_eq hsum
    have hfb : ((ξ (Fin.castSucc b) (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec (Fin.castSucc b) =
        (lf D F0).fl.e b := by
      rw [hξd]
      simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [← hfb, h2]
    exact Submodule.sub_mem _ hS hR

  obtain ⟨cl, -, hcl1, hcleq⟩ := hlc.1 P
  have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => cl a • (lf D F0).fl.e a)) := by
    rw [← hcleq]
    exact le_locP _ _ hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => cl a • (lf D F0).fl.e a) := hxl
  apply mem_localization_of_smul_mem' P.asIdeal _ x s hs
  refine Submodule.span_le.2 ?_ hsx
  rintro _ ⟨a, rfl⟩
  simp only [hcl1 hgP a, one_smul]
  exact key _ a rfl

end D7

end PI.UnitaryGroupMassFormula.BetaModX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.MemOrth
section
noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section Q

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T' : E}

theorem mem_orth' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem herm' (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← S.herm.eq x y, starRingEnd_apply]

theorem hXz (F' : LFlag S r T') : ∀ x ∈ Xsp F', S.hT x F'.fl.z = 0 := by
  intro x hx
  change x ∈ Submodule.span E (Set.range F'.fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact F'.fl.z_orth j
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]

theorem hzX (F' : LFlag S r T') : ∀ x ∈ Xsp F', S.hT F'.fl.z x = 0 := by
  intro x hx
  rw [herm', hXz F' x hx, star_zero]

abbrev Uo (F' : LFlag S r T') : Submodule E S.V := orth S (Xsp F')

abbrev Pk (F' : LFlag S r T') : Submodule E (Uo F') := (Xsp F').comap (Uo F').subtype

abbrev Qt (F' : LFlag S r T') : Type := (Uo F') ⧸ (Pk F')

def hV (F' : LFlag S r T') (c : E) : S.V →ₗ⋆[E] S.V →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E)
    (fun a b => S.hT a b + c * (S.hT a F'.fl.z * S.hT F'.fl.z b))
    (fun a a' b => by simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (fun t a b => by simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun a b b' => by simp only [map_add (f := _)]; ring)
    (fun t a b => by simp only [map_smul, smul_eq_mul, RingHom.id_apply]; ring)

theorem hV_apply (F' : LFlag S r T') (c : E) (a b : S.V) :
    hV F' c a b = S.hT a b + c * (S.hT a F'.fl.z * S.hT F'.fl.z b) := rfl

def hU (F' : LFlag S r T') (c : E) : Uo F' →ₗ⋆[E] Uo F' →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun a b => hV F' c (a : S.V) (b : S.V))
    (fun a a' b => by simp)
    (fun t a b => by simp)
    (fun a b b' => by simp)
    (fun t a b => by simp)

theorem hU_apply (F' : LFlag S r T') (c : E) (a b : Uo F') : hU F' c a b = hV F' c a b := rfl

theorem hU_left (F' : LFlag S r T') (c : E) (a b : Uo F') (ha : (a : S.V) ∈ Xsp F') : hU F' c a b = 0 := by
  rw [hU_apply, hV_apply, (mem_orth'.mp b.2) a ha, hXz F' a ha]
  ring

theorem hU_right (F' : LFlag S r T') (c : E) (a b : Uo F') (hb : (b : S.V) ∈ Xsp F') : hU F' c a b = 0 := by
  rw [hU_apply, hV_apply, herm' (b : S.V) (a : S.V), (mem_orth'.mp a.2) b hb, hzX F' b hb]
  simp

def hQ1 (F' : LFlag S r T') (c : E) : Qt F' →ₗ[E] Uo F' →ₗ⋆[E] E :=
  (Pk F').liftQ (hU F' c).flip (by
    intro b hb
    rw [LinearMap.mem_ker]
    ext a
    exact hU_right F' c a b hb)

def hQ (F' : LFlag S r T') (c : E) : Qt F' →ₗ⋆[E] Qt F' →ₗ[E] E :=
  (Pk F').liftQ (hQ1 F' c).flip (by
    intro a ha
    rw [LinearMap.mem_ker]
    ext b
    exact hU_left F' c a b ha)

theorem hQ_mk (F' : LFlag S r T') (c : E) (a b : Uo F') :
    hQ F' c (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = hV F' c a b := rfl

end Q

end PI.UnitaryGroupMassFormula.BetaModX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.PositiveWeightHolds
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section D7

open PI.UnitaryGroupMassFormula.BetaLUniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem positive_weight_holds : PosW := by
  intro D T' F' τ w hT' hw hwX
  by_contra hneg
  push_neg at hneg
  classical
  have hτ : ∀ a : D.host.E, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have hTE : ((T' : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hT'.ne'
  have hsymm : ∀ x y : (hS D).V, (hS D).hT y x = star ((hS D).hT x y) := by
    intro x y
    rw [← (hS D).herm.eq x y, starRingEnd_apply]
  have horth := (mem_orth (hS D)).1 hw
  have hez : ∀ a, (hS D).hT (F'.fl.e a) F'.fl.z = 0 := F'.fl.z_orth
  have hze : ∀ a, (hS D).hT F'.fl.z (F'.fl.e a) = 0 := by
    intro a; rw [hsymm, hez, star_zero]
  have hXz : ∀ x ∈ Xsp F', (hS D).hT x F'.fl.z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hez a
    | zero => simp
    | add y y' _ _ h1 h2 => simp [h1, h2]
    | smul c y _ h1 => simp [h1]
  have hzX : ∀ x ∈ Xsp F', (hS D).hT F'.fl.z x = 0 := by
    intro x hx; rw [hsymm, hXz x hx, star_zero]
  have hzz : (hS D).hT F'.fl.z F'.fl.z = -((T' : ℕ) : D.host.E) := F'.fl.z_norm
  have he_mem : ∀ a, F'.fl.e a ∈ Xplus F' := fun a =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  have hz_mem : F'.fl.z ∈ Xplus F' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hew : ∀ a, (hS D).hT (F'.fl.e a) w = 0 := fun a => horth _ (he_mem a)
  have hzw : (hS D).hT F'.fl.z w = 0 := horth _ hz_mem
  have hwe : ∀ a, (hS D).hT w (F'.fl.e a) = 0 := by intro a; rw [hsymm, hew, star_zero]
  have hwz : (hS D).hT w F'.fl.z = 0 := by rw [hsymm, hzw, star_zero]
  have hzX' : F'.fl.z ∉ Submodule.span D.host.E (Set.range F'.fl.e) := by
    intro h
    have := hXz _ h
    rw [hzz] at this
    exact hTE (neg_eq_zero.1 this)
  have hwX' : w ∉ Submodule.span D.host.E
      (Set.range (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V)) := by
    intro h
    have hle : Submodule.span D.host.E
        (Set.range (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V)) ≤
        Xsp F' ⊔ Submodule.span D.host.E {F'.fl.z} := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hle h)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have h0 : (hS D).hT F'.fl.z (x + c • F'.fl.z) = 0 := by rw [hxy]; exact hzw
    rw [map_add (f := _), hzX x hx, map_smul, hzz, zero_add, smul_eq_mul] at h0
    have hc : c = 0 := by
      rcases mul_eq_zero.1 h0 with h' | h'
      · exact h'
      · exact absurd (neg_eq_zero.1 h') hTE
    apply hwX
    rw [← hxy, hc, zero_smul, add_zero]
    exact hx
  let u : Fin (D.R.rS + 1 + 1) → (hS D).V :=
    Fin.snoc (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V) w
  have hu : LinearIndependent D.host.E u :=
    linearIndependent_finSnoc.2 ⟨linearIndependent_finSnoc.2 ⟨F'.fl.e_indep, hzX'⟩, hwX'⟩
  have hsig : Formalism.UG.HasSignature (((hS D).gram).map τ) (D.R.k + D.R.rS) (D.R.rS + 1) := by
    have h := D.sp.Y_sig 0 τ
    rw [D.sp.baseSpace_signature_eq τ] at h
    exact h
  obtain ⟨hcard, Q, hQ⟩ := wa_sig_data _ _ _ hsig
  have hdim := wa_neg_dim (((hS D).gram).map τ) Q hQ hcard (fun k => wa_cv (hS D) τ (u k))
    (fun x hx => wa_indep u hu x hx) (by
      intro x
      rw [wa_comb hτ x u]
      simp only [Fin.sum_univ_castSucc, u, Fin.snoc_castSucc, Fin.snoc_last, F'.fl.e_iso, hez, hze, hew,
        hwe, hzw, hwz, hzz, map_zero, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
      have h1 : ∀ c : ℂ, starRingEnd ℂ c * c = (Complex.normSq c : ℂ) := by
        intro c; rw [mul_comm]; exact Complex.mul_conj c
      rw [h1, h1, map_neg, map_natCast]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
        Complex.neg_im, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, mul_zero]
      have := Complex.normSq_nonneg (x (Fin.castSucc (Fin.last D.R.rS)))
      have := Complex.normSq_nonneg (x (Fin.last (D.R.rS + 1)))
      have : (0 : ℝ) ≤ (T' : ℝ) := Nat.cast_nonneg _
      nlinarith)
  omega

end D7

end PI.UnitaryGroupMassFormula.BetaModX
end
end

