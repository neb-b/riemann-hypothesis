module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ActsByFrameAct
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.HTOsmulRight

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.DiffIdealNeBot
section
noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem diffIdeal_ne_bot (D : D7) :
    Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ := by
  have h0 : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥ := by
    first
      | exact differentIdeal_ne_bot
      | exact differentIdeal_ne_bot (A := ℤ)
  first
    | exact Ideal.map_ne_bot_of_ne_bot h0
    | exact fun h => h0 ((Ideal.map_eq_bot_iff_of_injective
        (NoZeroSMulDivisors.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))).mp h)
    | exact fun h => h0 ((Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))).mp h)

theorem one_mem_ddS_neg (D : D7) (m : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hpow : ddS D ^ m = ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
      (differentIdeal ℤ (𝓞 D.host.F)) ^ m : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [ddS, FractionalIdeal.coeIdeal_pow]
  have hI : ddS D ^ m ≠ 0 := by
    rw [hpow, Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact pow_ne_zero _ (diffIdeal_ne_bot D)
  have hle : ddS D ^ m ≤ 1 := by
    rw [hpow]
    exact FractionalIdeal.coeIdeal_le_one
  rw [zpow_neg, zpow_natCast, ← FractionalIdeal.one_le]
  have h1 := FractionalIdeal.inv_anti_mono hI hle
  rwa [inv_one] at h1

theorem e_mem_lam (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : IsRowLat D F0 Λ) (a : Fin D.R.rS) : F0.e a ∈ Λ := by
  have hx : F0.e a ∈ XS D F0 := by
    apply Submodule.subset_span
    refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
    have h1 := one_mem_ddS_neg D (D.R.rS - (a : ℕ))
    rwa [Nat.cast_sub a.isLt.le] at h1
  rw [← hΛ.2.2] at hx
  exact (Submodule.mem_inf.mp hx).1

end PI.NRL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.FrameActOneAdd
section
noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem Xflag_mono (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) ≤ Submodule.span E (F.fl.e '' {i | i.1 < j + 1})
  exact Submodule.span_mono (Set.image_mono fun i hi => by
    simp only [Set.mem_setOf_eq] at hi ⊢
    omega)

theorem X_le_orth (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := by
  intro x hx
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y hy
  refine span_zero (φ := S.hT y) (fun z hz => ?_) hx
  obtain ⟨i, rfl⟩ := hz
  rw [herm_eq, span_zero (φ := S.hT (F.fl.e i)) (fun z hz => by
    obtain ⟨k, rfl⟩ := hz
    exact F.fl.e_iso i k) hy, star_zero]

theorem NLam_mul (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) {n₁ n₂ : S.V ≃ₗ[E] S.V}
    (h₁ : n₁ ∈ NLam Λ F) (h₂ : n₂ ∈ NLam Λ F) : n₁ * n₂ ∈ NLam Λ F := by
  simp only [NLam, IsAutLam, Set.mem_setOf_eq] at h₁ h₂ ⊢
  obtain ⟨⟨hi₁, hg₁⟩, hf₁, ho₁⟩ := h₁
  obtain ⟨⟨hi₂, hg₂⟩, hf₂, ho₂⟩ := h₂
  refine ⟨⟨Subgroup.mul_mem _ hi₁ hi₂, ?_⟩, ?_, ?_⟩
  · rw [gmap_eq_iff] at hg₁ hg₂ ⊢
    refine ⟨fun y hy => hg₁.1 _ (hg₂.1 y hy), fun y hy => ?_⟩
    obtain ⟨w₁, hw₁, rfl⟩ := hg₁.2 y hy
    obtain ⟨w₂, hw₂, rfl⟩ := hg₂.2 w₁ hw₁
    exact ⟨w₂, hw₂, rfl⟩
  · intro j x hx
    have h2 := hf₂ j x hx
    have hmem : n₂ x ∈ Xflag F (j + 1) := by
      have h3 := Submodule.add_mem _ (Xflag_mono F j h2) hx
      rwa [sub_add_cancel] at h3
    have h1 := hf₁ j (n₂ x) hmem
    have h4 := Submodule.add_mem _ h1 h2
    rw [sub_add_sub_cancel] at h4
    exact h4
  · intro x hx
    have h2 := ho₂ x hx
    have hmem : n₂ x ∈ orth S (Xsp F) := by
      have h3 := Submodule.add_mem _ (X_le_orth F h2) hx
      rwa [sub_add_cancel] at h3
    have h1 := ho₁ (n₂ x) hmem
    have h4 := Submodule.add_mem _ h1 h2
    rw [sub_add_sub_cancel] at h4
    exact h4

theorem modG_of_mem (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {x : S.V}
    (hx : x ∈ Ideal.span {(g : 𝓞 E)} • Λ) : ModG S Λ g x := by
  intro P hP
  haveI := P.isPrime
  show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ
  exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

theorem modG_add (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {x y : S.V} (hx : ModG S Λ g x) (hy : ModG S Λ g y) :
    ModG S Λ g (x + y) := by
  intro P hP
  exact Submodule.add_mem _ (hx P hP) (hy P hP)

theorem modG_map (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (n : S.V ≃ₗ[E] S.V) (hn : Formalism.HermitianLatticesTheory.gmap n Λ = Λ)
    {x : S.V} (hx : ModG S Λ g x) : ModG S Λ g (n x) := by
  intro P hP
  have hx' := hx P hP
  haveI := P.isPrime
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ := hx'
  show ∃ s ∈ P.asIdeal.primeCompl, s • n x ∈ Ideal.span {(g : 𝓞 E)} • Λ
  refine ⟨s, hs, ?_⟩
  have hmap : (Ideal.span {(g : 𝓞 E)} • Λ).map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) =
      Ideal.span {(g : 𝓞 E)} • Λ := by
    rw [Submodule.map_smul'']
    unfold Formalism.HermitianLatticesTheory.gmap at hn
    rw [hn]
  have hmem := Submodule.mem_map_of_mem (f := (n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) hsx
  rw [hmap] at hmem
  have he : ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) (s • x) = s • n x :=
    map_smul ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) s x
  rw [he] at hmem
  exact hmem

theorem frameAct_mem (Λ : Submodule (𝓞 E) S.V) {n : ℕ} (f : Fin n → S.V) (hf : ∀ c, f c ∈ Λ)
    (Q : Matrix (Fin n) (Fin n) (𝓞 E)) (b : Fin n) : frameAct f Q b ∈ Λ := by
  unfold frameAct
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [smul_coe]
  exact Λ.smul_mem _ (hf a)

theorem frameAct_one_add {n : ℕ} (f : Fin n → S.V) (g : 𝓞 E) (Q : Matrix (Fin n) (Fin n) (𝓞 E)) (b : Fin n) :
    frameAct f (1 + g • Q) b = f b + g • frameAct f Q b := by
  have h1 := frameAct_one f b
  unfold frameAct at h1 ⊢
  simp only [smul_coe] at h1 ⊢
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib, h1,
    mul_smul, Finset.smul_sum]

theorem exists_undo (Λ : Submodule (𝓞 E) S.V) (hint : IntLat Λ) (F : LFlag S r T) (g : 𝓞 E)
    (hrow : ∀ (a : Fin r) (t : Fin (r + 1) → 𝓞 E), ∃ v ∈ Λ, ∃ l : 𝓞 E,
      (l : E) + star (l : E) = -S.hT v v ∧ (∀ i, i ≤ a → S.hT v (F.fl.e i) = 0) ∧
      ∀ c, Fin.castSucc a < c → ∃ q : 𝓞 E, S.hT v (frame F c) = ((t c + g * q : 𝓞 E) : E))
    (hfe : ∀ a, F.fl.e a ∈ Λ)
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (hξ : UniUp ξ) :
    ∃ n ∈ NLam Λ F, ∃ M, ActsBy n (frame F) M ∧ ∃ Q, M * ξ = 1 + g • Q := by
  have hone : (1 : S.V ≃ₗ[E] S.V) ∈ NLam Λ F := by
    simp only [NLam, IsAutLam, Set.mem_setOf_eq]
    refine ⟨⟨Subgroup.one_mem _, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩
    · rw [gmap_eq_iff]
      exact ⟨fun y hy => hy, fun y hy => ⟨y, hy, rfl⟩⟩
    · show x - x ∈ _
      rw [sub_self]
      exact Submodule.zero_mem _
    · show x - x ∈ _
      rw [sub_self]
      exact Submodule.zero_mem _
  have hrow' : ∀ a : Fin (r + 1), a.val < r → ∀ t : Fin (r + 1) → 𝓞 E, ∃ w : Fin (r + 1) → 𝓞 E,
      (∀ c, c ≤ a → w c = 0) ∧ (∀ c, a < c → ∃ q, w c = t c + g * q) ∧
      (∃ n ∈ NLam Λ F, ActsBy n (frame F) (1 + rowMat a w)) := by
    intro a ha t
    obtain ⟨v, hv, l, hl, hperp, hcong⟩ := hrow ⟨a.val, ha⟩ t
    have hca : Fin.castSucc (⟨a.val, ha⟩ : Fin r) = a := Fin.ext rfl
    rw [hca] at hcong
    choose q hq using hcong
    let w : Fin (r + 1) → 𝓞 E := fun c => if h : a < c then t c + g * q c h else 0
    have hee : S.hT (F.fl.e ⟨a.val, ha⟩) (F.fl.e ⟨a.val, ha⟩) = 0 := F.fl.e_iso _ _
    have hve : S.hT v (F.fl.e ⟨a.val, ha⟩) = 0 := hperp _ le_rfl
    have hev : S.hT (F.fl.e ⟨a.val, ha⟩) v = 0 := by rw [herm_eq, hve, star_zero]
    have hw : ∀ c, S.hT v (frame F c) = (w c : E) := by
      intro c
      by_cases hc : a < c
      · simp only [w, dif_pos hc]
        exact hq c hc
      · simp only [w, dif_neg hc]
        have hcr : c.val < r := by
          have h' : ¬ a.val < c.val := fun h => hc (Fin.lt_def.mpr h)
          omega
        obtain ⟨c', rfl⟩ : ∃ c' : Fin r, Fin.castSucc c' = c := ⟨⟨c.val, hcr⟩, Fin.ext rfl⟩
        have hfc : frame F (Fin.castSucc c') = F.fl.e c' := by
          show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc c') = F.fl.e c'
          exact Fin.snoc_castSucc ..
        have hle : c' ≤ (⟨a.val, ha⟩ : Fin r) := by
          have h' : ¬ a.val < c'.val := fun h => hc (Fin.lt_def.mpr (by simpa using h))
          exact Fin.le_def.mpr (by simp only; omega)
        rw [hfc, hperp c' hle]
        simp
    refine ⟨w, fun c hc => ?_, fun c hc => ⟨q c hc, by simp only [w, dif_pos hc]⟩, ?_⟩
    · have hnc : ¬ a < c := not_lt.mpr hc
      simp only [w, dif_neg hnc]
    · refine ⟨tvEquiv (F.fl.e ⟨a.val, ha⟩) v (l : E) hee hev hve,
        tv_mem_NLam Λ hint F ⟨a.val, ha⟩ (hfe _) v hv hperp l hl hee hev hve, ?_⟩
      have hact := tv_actsBy F ⟨a.val, ha⟩ v (l : E) hee hev hve w hw
      rw [hca] at hact
      exact hact
  obtain ⟨M, ⟨n, hn, hact⟩, Q, hQ⟩ := row_elim g (fun M => ∃ n ∈ NLam Λ F, ActsBy n (frame F) M)
    ⟨1, hone, actsBy_one _⟩
    (fun M N hM hN => by
      obtain ⟨n₁, h₁, a₁⟩ := hM
      obtain ⟨n₂, h₂, a₂⟩ := hN
      exact ⟨n₁ * n₂, NLam_mul Λ F h₁ h₂, actsBy_mul a₁ a₂⟩)
    hrow' ξ hξ
  exact ⟨n, hn, M, hact, Q, hQ⟩

end PI.NRL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ResidueOnto
section
noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

section Prime

variable (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hint : IntLat Λ)
  (e : Fin r → S.V) (hind : LinearIndependent E e) (he : ∀ i, e i ∈ Λ) (P : HeightOneSpectrum (𝓞 E))
  (hloc : ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range e) →
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Submodule.span (𝓞 E) (Set.range e))

include hU hint hind he hloc in
theorem residue_onto (c : Fin r) :
    ∃ y ∈ Λ, ∃ o : Fin r → 𝓞 E, (∀ i, S.hT y (e i) = (o i : E)) ∧
      ∀ i, (o i - if i = c then 1 else 0) ∈ P.asIdeal := by
  haveI := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let mk := Ideal.Quotient.mk P.asIdeal
  let U : Submodule (𝓞 E ⧸ P.asIdeal) (Fin r → 𝓞 E ⧸ P.asIdeal) :=
    { carrier := {φ | ∃ y ∈ Λ, ∃ o : Fin r → 𝓞 E, (∀ i, S.hT y (e i) = (o i : E)) ∧ ∀ i, φ i = mk (o i)}
      zero_mem' := ⟨0, Λ.zero_mem, 0, fun i => by simp, fun i => by simp⟩
      add_mem' := by
        rintro φ ψ ⟨y, hy, o, ho, hφ⟩ ⟨y', hy', o', ho', hψ⟩
        refine ⟨y + y', Λ.add_mem hy hy', o + o', fun i => ?_, fun i => ?_⟩
        · simp [map_add (f := _), ho, ho']
        · simp [hφ, hψ]
      smul_mem' := by
        rintro κ φ ⟨y, hy, o, ho, hφ⟩
        obtain ⟨κ', rfl⟩ := Ideal.Quotient.mk_surjective κ
        refine ⟨cj κ' • y, Λ.smul_mem _ hy, fun i => κ' * o i, fun i => ?_, fun i => ?_⟩
        · rw [hT_cj_left, ho]; push_cast; ring
        · simp [hφ, mk] }
  have hUtop : U = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfU⟩ := Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.mpr hne)
    let α : Fin r → 𝓞 E ⧸ P.asIdeal := fun i => f (fun j => if i = j then 1 else 0)
    have hfα : ∀ φ, f φ = ∑ i, φ i * α i := by
      intro φ
      rw [LinearMap.pi_apply_eq_sum_univ f φ]
      simp [α, smul_eq_mul]
    have hα0 : ∃ i, α i ≠ 0 := by
      by_contra h
      push Not at h
      apply hf0
      refine LinearMap.ext fun φ => ?_
      rw [hfα, LinearMap.zero_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]
    choose α' hα' using fun i => Ideal.Quotient.mk_surjective (α i)
    have hmem := coeff_mem_P Λ hU e hind P hloc α' (by
      intro y hy
      choose o ho using fun i => hint y hy (e i) (he i)
      have hφ : (fun i => mk (o i)) ∈ U := ⟨y, hy, o, ho, fun i => rfl⟩
      have hz : f (fun i => mk (o i)) = 0 := hfU hφ
      rw [hfα] at hz
      refine ⟨∑ i, o i * α' i, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem]
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum, map_mul, hα', mk] using hz
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hT_osmul_right, ho]; ring)
    obtain ⟨i, hi⟩ := hα0
    apply hi
    rw [← hα' i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
  have hc : (fun i => if i = c then (1 : 𝓞 E ⧸ P.asIdeal) else 0) ∈ U := by rw [hUtop]; trivial
  obtain ⟨y, hy, o, ho, hφ⟩ := hc
  refine ⟨y, hy, o, ho, fun i => ?_⟩
  rw [← Ideal.Quotient.eq]
  have := hφ i
  simp only at this
  by_cases hic : i = c
  · simp only [hic, if_true] at this ⊢; rw [map_one]; exact this.symm
  · simp only [hic, if_false] at this ⊢; rw [map_zero]; exact this.symm

include hU hint hind he hloc in
theorem exact_dual (c : Fin r) :
    ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (e i) = 0) ∧ ∃ o : 𝓞 E, S.hT y (e c) = (o : E) ∧ o ∉ P.asIdeal := by
  choose y hy o ho hP using fun j => residue_onto Λ hU hint e hind he P hloc j
  let G : Matrix (Fin r) (Fin r) (𝓞 E) := fun j i => o j i
  have hdet : G.det ∉ P.asIdeal := by
    intro hmem
    have h1 : (Ideal.Quotient.mk P.asIdeal).mapMatrix G = 1 := by
      ext j i
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
      have := Ideal.Quotient.eq.mpr (hP j i)
      rw [this]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    have := RingHom.map_det (Ideal.Quotient.mk P.asIdeal) G
    rw [h1, Matrix.det_one, Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at this
    exact zero_ne_one this
  have key : ∀ i, S.hT (∑ j, cj (G.adjugate c j) • y j) (e i) = ((G.adjugate * G) c i : E) := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT_cj_left, ho]
  rw [Matrix.adjugate_mul] at key
  refine ⟨∑ j, cj (G.adjugate c j) • y j, Λ.sum_mem fun j _ => Λ.smul_mem _ (hy j), fun i hi => ?_,
    G.det, ?_, hdet⟩
  · rw [key, Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hi)]; simp
  · rw [key, Matrix.smul_apply, Matrix.one_apply_eq]; simp

end Prime

end PI.NRL
end
end

