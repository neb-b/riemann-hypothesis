module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.LocalAssemblyPrincipal
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

def IsInt (I : Formalism.MainNotions.S.AutInst) (x : I.E) : Prop := ∃ a : 𝓞 I.E, (a : I.E) = x

section Int

variable (I : Formalism.MainNotions.S.AutInst)

theorem isInt_coe (a : 𝓞 I.E) : IsInt I (a : I.E) := ⟨a, rfl⟩

theorem isInt_mul {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by push_cast; rfl⟩

theorem isInt_sub {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; rfl⟩

theorem isInt_add {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

theorem isInt_one : IsInt I (1 : I.E) := ⟨1, by simp⟩

theorem isInt_hG {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) : IsInt I (hG I x y) := by
  obtain ⟨a, ha⟩ := (I.L_dual y).1 hy x hx
  exact ⟨a, ha⟩

theorem isInt_star (θ : 𝓞 I.E) : IsInt I (star (θ : I.E)) :=
  ⟨⟨star (θ : I.E), (RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩

theorem natCast_mem_Ap (p s : ℕ) : (s : I.E) ∈ Ap I p := by
  refine ⟨1, Nat.coprime_one_left p, (s : 𝓞 I.E), ?_⟩
  simp

end Int

theorem local_assembly_principal : PPAssemble := by
  unfold PPAssemble
  intro I p m r k θ e f M w wd hp hm hH hw hew hwd hspan
  obtain ⟨-, -, hθ, -, -, -, -, hMc, -⟩ := hH
  obtain ⟨hθ1, hθ2, hθ3⟩ := hθ
  have hm0 : m ≠ 0 := by omega
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hMp : Nat.Coprime M p := Nat.Coprime.coprime_dvd_right (dvd_pow_self p hm0) hMc
  have hM0 : (M : I.E) ≠ 0 := by
    have hM : M ≠ 0 := by
      rintro rfl
      exact hp1 ((Nat.coprime_zero_left _).1 hMp)
    exact_mod_cast hM

  choose sw hsw using fun i => LA_clear (I := I) p (hw i).1
  choose sd hsd using fun i => LA_clear (I := I) p (hw i).2
  have hT0p : Nat.Coprime ((∏ i, sw i) * ∏ i, sd i) p :=
    Nat.Coprime.mul_left (Nat.Coprime.prod_left fun i _ => (hsw i).1)
      (Nat.Coprime.prod_left fun i _ => (hsd i).1)
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = ((∏ i, sw i) * ∏ i, sd i) ^ Nat.totient (p ^ m) := ⟨_, rfl⟩
  have hTp : Nat.Coprime T p := hTdef ▸ Nat.Coprime.pow_left _ hT0p
  have hT0dvd : ((∏ i, sw i) * ∏ i, sd i) ∣ T :=
    hTdef ▸ dvd_pow_self _ (Nat.totient_pos.2 (pow_pos hp.pos m)).ne'
  have hTne : T ≠ 0 := by
    rintro h0
    rw [h0] at hTp
    exact hp1 ((Nat.coprime_zero_left _).1 hTp)
  have hTE : (T : I.E) ≠ 0 := by exact_mod_cast hTne
  have hTmod : T ≡ 1 [MOD p ^ m] := hTdef ▸ Nat.ModEq.pow_totient (Nat.Coprime.pow_right m hT0p)
  obtain ⟨c, hc⟩ : ∃ c, T = 1 + p ^ m * c := by
    have h1 : 1 ≤ T := Nat.one_le_iff_ne_zero.2 hTne
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' h1).1 hTmod.symm
    refine ⟨c, ?_⟩
    generalize p ^ m * c = q at hc ⊢
    omega
  have hT1 : QA I p (p ^ m) (1 - (T : I.E) ^ 2) := by
    apply QA_of_GE (I := I)
    refine ⟨-((c : 𝓞 I.E) + c + (p : 𝓞 I.E) ^ m * c * c), ?_⟩
    rw [hc]
    push_cast
    ring
  have hTA : (T : I.E) ^ 2 ∈ Ap I p := pow_mem (natCast_mem_Ap I p T) 2
  have hTw : ∀ i, (T : I.E) • w i ∈ I.L := by
    intro i
    obtain ⟨d, hd⟩ : sw i ∣ T := dvd_trans (dvd_trans (Finset.dvd_prod_of_mem sw (Finset.mem_univ i))
      (dvd_mul_right _ _)) hT0dvd
    rw [hd, Nat.cast_mul, mul_comm, mul_smul, natE_smul (I := I)]
    exact I.L.smul_mem _ (hsw i).2
  have hTwd : ∀ i, (T : I.E) • wd i ∈ I.L := by
    intro i
    obtain ⟨d, hd⟩ : sd i ∣ T := dvd_trans (dvd_trans (Finset.dvd_prod_of_mem sd (Finset.mem_univ i))
      (dvd_mul_left _ _)) hT0dvd
    rw [hd, Nat.cast_mul, mul_comm, mul_smul, natE_smul (I := I)]
    exact I.L.smul_mem _ (hsd i).2

  have hθ1s : GE I (p ^ m) (star (θ : I.E) * star (θ : I.E) - star (θ : I.E)) := by
    obtain ⟨t, ht⟩ := hθ1
    obtain ⟨ts, hts⟩ := isInt_star I t
    refine ⟨ts, ?_⟩
    have h := congrArg star ht
    simp only [star_sub, star_mul, star_natCast] at h
    rw [h, hts]
    ring
  obtain ⟨θs, hθs⟩ := isInt_star I θ
  obtain ⟨z, hzdef⟩ : ∃ z : Fin I.n → I.E,
      z = (T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k)) := ⟨_, rfl⟩
  have hz : z ∈ I.L := by
    rw [hzdef, smul_sub, smul_comm (T : I.E) (θ : I.E), smul_comm (T : I.E) (star (θ : I.E)), ← hθs]
    exact I.L.sub_mem (I.L.smul_mem θ (hTw _)) (I.L.smul_mem θs (hTwd _))
  have hl1 : hG I (wd (Fin.last k)) (w (Fin.last k)) = 1 := by
    simpa using hwd (Fin.last k) (Fin.last k)
  have hl2 : hG I (w (Fin.last k)) (wd (Fin.last k)) = 1 := by
    rw [hG_symm (I := I) (wd (Fin.last k)) (w (Fin.last k)), hl1, star_one]
  have hl3 : ∀ i : Fin k, hG I (wd (Fin.last k)) (w i.castSucc) = 0 := by
    intro i
    rw [hwd, if_neg (Fin.castSucc_ne_last i).symm]
  have hl4 : ∀ i : Fin k, hG I (w (Fin.last k)) (wd i.castSucc) = 0 := by
    intro i
    rw [hG_symm (I := I) (wd i.castSucc) (w (Fin.last k)), hwd, if_neg (Fin.castSucc_ne_last i), star_zero]
  unfold Concl
  refine ⟨z, fun i => (T : I.E) • w i.castSucc, fun i => (T : I.E) • wd i.castSucc, hz,
    fun i => ⟨hTw _, hTwd _⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hzdef]
    refine ⟨?_, ?_⟩ <;> rw [hG_smul_right, hG_sub_right, hG_smul_right, hG_smul_right]
    · rw [(hew a _).1, (hew a _).2.2.1]
      ring
    · rw [(hew a _).2.1, (hew a _).2.2.2]
      ring
  · intro a i
    simp [hG_smul_right, hew]
  ·
    apply GE_of_QA (I := I) p m (isInt_add I (isInt_hG I hz hz) (isInt_one I))
    have hzz : hG I z z + 1 =
        ((T : I.E) ^ 2 * (hG I (w (Fin.last k)) (w (Fin.last k)) + hG I (wd (Fin.last k)) (wd (Fin.last k))))
          * ((θ : I.E) * star (θ : I.E))
        - (T : I.E) ^ 2 * ((θ : I.E) * θ - θ)
        - (T : I.E) ^ 2 * (star (θ : I.E) * star (θ : I.E) - star (θ : I.E))
        + (T : I.E) ^ 2 * (1 - (θ : I.E) - star (θ : I.E))
        + (1 - (T : I.E) ^ 2) := by
      rw [hzdef]
      simp only [hG_smul_left, hG_smul_right, hG_sub_left, hG_sub_right, star_natCast, star_star, star_sub,
        star_smul]
      rw [hl1, hl2]
      ring
    rw [hzz]
    have hAD : (T : I.E) ^ 2 * (hG I (w (Fin.last k)) (w (Fin.last k)) + hG I (wd (Fin.last k)) (wd (Fin.last k)))
        ∈ Ap I p :=
      mul_mem hTA (add_mem (hG_mem_Ap (I := I) p (hw _).1 (hw _).1) (hG_mem_Ap (I := I) p (hw _).2 (hw _).2))
    refine QA_add (I := I) p _ (QA_add (I := I) p _ (QA_sub (I := I) p _ (QA_sub (I := I) p _
      (QA_mul (I := I) p _ hAD (QA_of_GE (I := I) p _ hθ2))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ1)))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ1s)))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ3))) hT1
  · intro i
    constructor
    · apply GE_of_QA (I := I) p m (isInt_mul I (isInt_coe I θ) (isInt_hG I hz (hTw _)))
      have h : (θ : I.E) * hG I z ((T : I.E) • w i.castSucc) =
          ((T : I.E) ^ 2 * hG I (w (Fin.last k)) (w i.castSucc)) * ((θ : I.E) * star (θ : I.E)) := by
        rw [hzdef]
        simp only [hG_smul_left, hG_smul_right, hG_sub_left, star_natCast, star_star, star_sub]
        rw [hl3]
        ring
      rw [h]
      exact QA_mul (I := I) p _ (mul_mem hTA (hG_mem_Ap (I := I) p (hw _).1 (hw _).1))
        (QA_of_GE (I := I) p _ hθ2)
    · apply GE_of_QA (I := I) p m
        (isInt_mul I (by rw [← hθs]; exact isInt_coe I θs) (isInt_hG I hz (hTwd _)))
      have h : star (θ : I.E) * hG I z ((T : I.E) • wd i.castSucc) =
          -((T : I.E) ^ 2 * hG I (wd (Fin.last k)) (wd i.castSucc)) * ((θ : I.E) * star (θ : I.E)) := by
        rw [hzdef]
        simp only [hG_smul_left, hG_smul_right, hG_sub_left, star_natCast, star_star, star_sub]
        rw [hl4]
        ring
      rw [h]
      exact QA_mul (I := I) p _ (neg_mem (mul_mem hTA (hG_mem_Ap (I := I) p (hw _).2 (hw _).2)))
        (QA_of_GE (I := I) p _ hθ2)
  · intro i j
    have h : hG I ((T : I.E) • wd i.castSucc) ((T : I.E) • w j.castSucc) =
        (T : I.E) ^ 2 * (if i = j then 1 else 0) := by
      rw [hG_smul_left, hG_smul_right, hwd, star_natCast]
      simp only [Fin.castSucc_inj]
      ring
    rw [h]
    by_cases hij : i = j
    · rw [if_pos hij, mul_one]
      apply GE_of_QA (I := I) p m
        (isInt_mul I (isInt_coe I θ) (isInt_sub I ⟨(T : 𝓞 I.E) ^ 2, by push_cast; rfl⟩ (isInt_one I)))
      have h2 : (θ : I.E) * ((T : I.E) ^ 2 - 1) = -(θ : I.E) * (1 - (T : I.E) ^ 2) := by ring
      rw [h2]
      exact QA_mul (I := I) p _ (neg_mem (int_mem_Ap (I := I) p θ)) hT1
    · rw [if_neg hij]
      exact ⟨0, by simp⟩
  · exact span_part (I := I) p m r k θ e f M T w wd hMp hM0 hTp hTE hθ1 hθ2 hθ3 hw hspan _
      (fun a => Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩))))
      (fun a => Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩))))
      (Or.inl (Or.inl (Or.inr hzdef.symm)))
      (fun i => Or.inl (Or.inr ⟨i, rfl⟩))
      (fun i => Or.inr ⟨i, rfl⟩)

end PI.ScRefExists.PPA
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WFrameOf
section
noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WF

variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}

section Frame

variable {r k : ℕ} {e f : Fin r → Fin I.n → I.E} {w : Fin (k + 1) → Fin I.n → I.E}

def fam (e f : Fin r → Fin I.n → I.E) (w : Fin (k + 1) → Fin I.n → I.E) :
    Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → Fin I.n → I.E :=
  Sum.elim e (Sum.elim f w)

theorem fam_li (he : ∀ a b, hG I (e a) (e b) = 0) (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0)
    (hw : ∀ i a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0) (hli : LinearIndependent I.E w) :
    LinearIndependent I.E (fam e f w) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [fam, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hg
  have hfe : ∀ a b, hG I (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hG_symm I (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hb : ∀ a, g (Sum.inr (Sum.inl a)) = 0 := by
    intro a
    have hw1 : ∀ i, hG I (e a) (w i) = 0 := fun i => (hw i a).1
    have h1 := congrArg (hG I (e a)) hg
    simpa [hG_add_right, hG_sum_right, hG_smul_right, he, hef, hw1, hG_zero_right] using h1
  have ha : ∀ a, g (Sum.inl a) = 0 := by
    intro a
    have hw2 : ∀ i, hG I (f a) (w i) = 0 := fun i => (hw i a).2
    have h1 := congrArg (hG I (f a)) hg
    simpa [hG_add_right, hG_sum_right, hG_smul_right, hf, hfe, hw2, hG_zero_right] using h1
  simp only [ha, hb, zero_smul, Finset.sum_const_zero, zero_add] at hg
  have hc := Fintype.linearIndependent_iff.1 hli (fun i => g (Sum.inr (Sum.inr i))) hg
  intro i
  rcases i with a | a | i
  · exact ha a
  · exact hb a
  · exact hc i

theorem fam_sp (hp : p.Prime) (he : ∀ a b, hG I (e a) (e b) = 0) (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p)
    (hW : ∀ x ∈ LA I p, (∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0) →
        x ∈ Submodule.span (Ap I p) (Set.range w)) :
    ⊤ ≤ Submodule.span I.E (Set.range (fam e f w)) := by
  rw [← I.L_span, Submodule.span_le]
  intro y hy
  have hyA : y ∈ LA I p := L_le_LA hy
  have hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w) := by
    apply hW _ (sub_mem hyA (proj_mem hp heA hfA hyA))
    intro a
    rw [hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]
    exact ⟨rfl, rfl⟩
  have key : ∀ z ∈ Submodule.span (Ap I p) (Set.range w),
      z ∈ Submodule.span I.E (Set.range (fam e f w)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨Sum.inr (Sum.inr i), rfl⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact Submodule.smul_mem _ (c : I.E) hx
  have hp' : proj e f y ∈ Submodule.span I.E (Set.range (fam e f w)) := by
    unfold proj
    refine Submodule.sum_mem _ fun a _ => add_mem ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inl a), rfl⟩)
  have := add_mem hp' (key _ hz)
  simpa using this

end Frame

theorem wFrame_of (hPID : ApPID) (hWB : WBasis) : WFrame := by
  intro I p r k e f M hp hn he hf hef hM heM
  obtain ⟨w, hw1, hwli, hwsp⟩ := hWB I p r k e f M hp (hPID I p hp) hn he hf hef hM heM
  have heA : ∀ a, e a ∈ LA I p := fun a => mem_LA_of_nsmul hp hM (heM a).1
  have hfA : ∀ a, f a ∈ LA I p := fun a => mem_LA_of_nsmul hp hM (heM a).2
  have hwA : ∀ i, w i ∈ LA I p := fun i => (hw1 i).1
  have hwo : ∀ i a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 := fun i a => (hw1 i).2 a
  have hli := fam_li he hf hef hwo hwli
  have hsp := fam_sp hp he hf hef heA hfA hwsp
  have hT0 : ∀ u, (∀ j, hG I (fam e f w j) u = 0) → u = 0 := by
    intro u hu
    apply hG_nondeg
    intro x
    have hx : x ∈ Submodule.span I.E (Set.range (fam e f w)) := hsp Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hu j
    | zero => exact hG_zero_left I u
    | add x y _ _ hx hy => rw [hG_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [hG_smul_left, hx, mul_zero]
  let T : (Fin I.n → I.E) →ₗ[I.E] (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E) :=
    { toFun := fun d j => hG I (fam e f w j) d
      map_add' := fun x y => by
        ext j
        simp [hG_add_right]
      map_smul' := fun c x => by
        ext j
        simp [hG_smul_right] }
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    exact hT0 u (fun j => congrFun hu j)
  have hdim : Module.finrank I.E (Fin I.n → I.E) =
      Module.finrank I.E (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E) := by
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hn]
    ring
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hTi
  have hex : ∀ i : Fin (k + 1), ∃ d : Fin I.n → I.E, ∀ j,
      hG I (fam e f w j) d = if j = Sum.inr (Sum.inr i) then 1 else 0 := by
    intro i
    obtain ⟨d, hd⟩ := hTs (fun j => if j = Sum.inr (Sum.inr i) then 1 else 0)
    exact ⟨d, fun j => congrFun hd j⟩
  choose wd hwd using hex
  have hewd : ∀ a i, hG I (e a) (wd i) = 0 := fun a i => by
    simpa [fam] using hwd i (Sum.inl a)
  have hfwd : ∀ a i, hG I (f a) (wd i) = 0 := fun a i => by
    simpa [fam] using hwd i (Sum.inr (Sum.inl a))
  have hwwd : ∀ j i, hG I (w j) (wd i) = if j = i then 1 else 0 := fun j i => by
    simpa [fam] using hwd i (Sum.inr (Sum.inr j))
  have hdual : ∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0 := by
    intro i j
    rw [hG_symm I (w j) (wd i), hwwd j i]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hyS : ∀ y ∈ I.L,
      y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) := by
    intro y hy
    have hyA : y ∈ LA I p := L_le_LA hy
    have hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w) := by
      apply hwsp _ (sub_mem hyA (proj_mem hp heA hfA hyA))
      intro a
      rw [hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]
      exact ⟨rfl, rfl⟩
    have h1 := proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range w)
      Set.subset_union_left
    have h2 : y - proj e f y ∈
        Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) :=
      Submodule.span_mono Set.subset_union_right hz
    have := add_mem h1 h2
    simpa using this
  have hwdAp : ∀ i, ∀ y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w),
      hG I (wd i) y ∈ Ap I p := by
    intro i y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨j, rfl⟩
      · rw [hG_symm I (e a) (wd i), hewd a i, star_zero]
        exact zero_mem _
      · rw [hG_symm I (f a) (wd i), hfwd a i, star_zero]
        exact zero_mem _
      · rw [hdual i j]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    | zero => rw [hG_zero_right]; exact zero_mem _
    | add x y _ _ hx hy => rw [hG_add_right]; exact add_mem hx hy
    | smul c x _ hx =>
      show hG I (wd i) ((c : I.E) • x) ∈ Ap I p
      rw [hG_smul_right]
      exact mul_mem c.2 hx
  have hwdA : ∀ i, wd i ∈ LA I p := fun i => dual_LA hp fun y hy => by
    rw [hG_symm I (wd i) y]
    exact star_mem_Ap (hwdAp i y (hyS y hy))
  have hyS' : ∀ y ∈ I.L,
      y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd) := by
    intro y hy
    have hyA : y ∈ LA I p := L_le_LA hy
    have hzA : y - proj e f y ∈ LA I p := sub_mem hyA (proj_mem hp heA hfA hyA)
    have hze : ∀ a, hG I (e a) (y - proj e f y) = 0 := fun a => by
      rw [hG_sub_right, hG_e_proj he hef, sub_self]
    have hzf : ∀ a, hG I (f a) (y - proj e f y) = 0 := fun a => by
      rw [hG_sub_right, hG_f_proj hf hef, sub_self]
    have hzeq : y - proj e f y = ∑ i, hG I (w i) (y - proj e f y) • wd i := by
      rw [← sub_eq_zero]
      apply hT0
      intro j
      rw [hG_sub_right, hG_sum_right]
      simp only [hG_smul_right]
      rcases j with a | a | j
      · simp [fam, hze a, hewd]
      · simp [fam, hzf a, hfwd]
      · simp [fam, hwwd]
    have hz' : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range wd) := by
      rw [hzeq]
      refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.smul_mem _ (⟨_, hG_LA hp (hwA i) hzA⟩ : Ap I p)
        (Submodule.subset_span ⟨i, rfl⟩)
    have h1 := proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range wd)
      Set.subset_union_left
    have h2 : y - proj e f y ∈
        Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd) :=
      Submodule.span_mono Set.subset_union_right hz'
    have := add_mem h1 h2
    simpa using this
  exact ⟨w, wd, fun i => ⟨hwA i, hwdA i⟩,
    fun a i => ⟨(hwo i a).1, (hwo i a).2, hewd a i, hfwd a i⟩, hdual,
    fun y hy => ⟨hyS y hy, hyS' y hy⟩⟩

end PI.ScRefExists.WF
end
end

