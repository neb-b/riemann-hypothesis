module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.FrameMemLocP

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.AdmissibleStableUnderFrameChange
section
noncomputable section

open scoped Classical

namespace PI.TCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ y ∈ U, S.hT y v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem z_mem_orth {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  rw [mem_orth]
  intro y hy
  have hy' : y ∈ Submodule.span E (Set.range F.fl.e) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact F.fl.z_orth a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem coef_exists {T : E} (F : LFlag S r T) (n : S.V ≃ₗ[E] S.V)
    (h1 : ∀ j, ∀ x ∈ Xflag F (j + 1), n x - x ∈ Xflag F j)
    (h2 : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) (b : Fin (r + 1)) :
    ∃ c : Fin r → E, (∀ k : Fin r, (b : ℕ) ≤ k → c k = 0) ∧
      ∑ k, c k • F.fl.e k = n (frame F b) - frame F b := by
  induction b using Fin.lastCases with
  | last =>
    have hv := h2 _ (z_mem_orth F)
    have hv' : n F.fl.z - F.fl.z ∈ Submodule.span E (Set.range F.fl.e) := hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hv'
    refine ⟨c, fun k hk => absurd hk (by simp), ?_⟩
    rw [frame_last, hc]
  | cast i =>
    rw [frame_castSucc]
    have hmem : F.fl.e i ∈ Xflag F ((i : ℕ) + 1) :=
      Submodule.subset_span ⟨i, (by simp : (i : ℕ) < (i : ℕ) + 1), rfl⟩
    have hv : n (F.fl.e i) - F.fl.e i ∈ Submodule.span E (F.fl.e '' {k | (k : ℕ) < i}) := h1 _ _ hmem
    obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination E).mp hv
    refine ⟨l, fun k hk => ?_, ?_⟩
    · exact (Finsupp.mem_supported' E l).mp hl k (by simpa using hk)
    · rw [← hlc, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]

theorem coef {T : E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (hz : F.fl.z ∈ Λ)
    (hc : IsFixedConv Λ g F) (n : S.V ≃ₗ[E] S.V) (hn : n ∈ NLam Λ F) :
    ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, UT B ∧ (∀ b, n (frame F b) = frE (frame F) B b) ∧
      ∀ P : HeightOneSpectrum (𝓞 E), ((g : 𝓞 E) ∈ P.asIdeal) →
        ∀ a b, (haveI := P.isPrime; B a b ∈ locInt P.asIdeal) := by
  obtain ⟨⟨_, hΛ⟩, h1, h2⟩ := hn
  have hnΛ : ∀ y ∈ Λ, n y ∈ Λ := by
    intro y hy
    rw [← hΛ]
    exact Submodule.mem_map_of_mem hy
  choose c hc0 hcs using coef_exists F n h1 h2
  let ν : Matrix (Fin (r + 1)) (Fin (r + 1)) E := fun a b => if h : (a : ℕ) < r then c b ⟨a, h⟩ else 0
  have hν0 : ∀ a b, b ≤ a → ν a b = 0 := by
    intro a b hba
    simp only [ν]
    split_ifs with h
    · exact hc0 b ⟨a, h⟩ (by simpa using hba)
    · rfl
  have hνsum : ∀ b, ∑ a, ν a b • frame F a = n (frame F b) - frame F b := by
    intro b
    rw [Fin.sum_univ_castSucc, ← hcs b]
    simp [ν, frame_castSucc]
  have hint : ∀ P : HeightOneSpectrum (𝓞 E), ((g : 𝓞 E) ∈ P.asIdeal) →
      ∀ b k, (haveI := P.isPrime; c b k ∈ locInt P.asIdeal) := by
    intro P hP b k
    haveI := P.isPrime
    have hf := frame_mem_locP Λ g F hz hc P hP b
    obtain ⟨s, hs, hsf⟩ := mem_locP.mp hf
    have hX : n (frame F b) - frame F b ∈ Xsp F := by
      rw [← hcs b]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have hloc : n (frame F b) - frame F b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
      refine mem_locP.mpr ⟨s, hs, ?_⟩
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [smul_sub, ← lin_osmul]
        exact Λ.sub_mem (hnΛ _ hsf) hsf
      · show s • (n (frame F b) - frame F b) ∈ Xsp F
        rw [osmul]
        exact Submodule.smul_mem _ _ hX
    obtain ⟨c', _, hc'1, heq⟩ := hc.1 P
    rw [heq] at hloc
    obtain ⟨t, ht, htv⟩ := mem_locP.mp hloc
    have hfun : (fun a => c' a • F.fl.e a) = F.fl.e := by
      funext a; rw [hc'1 hP a, one_smul]
    rw [hfun] at htv
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp htv
    have hsum : ∑ j, ((o j : E) - (t : E) * c b j) • F.fl.e j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have e1 : ∑ j, (o j : E) • F.fl.e j = ∑ j, o j • F.fl.e j := by simp only [osmul]
      rw [e1, ho, ← hcs b, osmul, Finset.smul_sum]
      simp only [smul_smul]
    have hk := Fintype.linearIndependent_iff.mp F.fl.e_indep _ hsum k
    exact ⟨t, ht, o k, by linear_combination -hk⟩
  refine ⟨1 + ν, ⟨fun a b hba => ?_, fun a => ?_⟩, fun b => ?_, fun P hP a b => ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hba).symm, hν0 a b hba.le, add_zero]
  · rw [Matrix.add_apply, Matrix.one_apply_eq, hν0 a a le_rfl, add_zero]
  · simp only [frE, Matrix.add_apply, add_smul, Finset.sum_add_distrib, hνsum b, Matrix.one_apply,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel
  · haveI := P.isPrime
    refine Subring.add_mem _ ?_ ?_
    · rw [Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · simp only [ν]
      split_ifs with h
      · exact hint P hP b ⟨a, h⟩
      · exact Subring.zero_mem _

theorem admissible_stable_under_frame_change {T T' : E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (x F₂ : LFlag S r T')
    (hFz : F.fl.z ∈ Λ) (hFc : IsFixedConv Λ g F) (hxz : x.fl.z ∈ Λ) (hxc : IsFixedConv Λ g x)
    (hadm : IsAdmissible Λ g F x) (n : S.V ≃ₗ[E] S.V) (hn : n ∈ NLam Λ F) (m : S.V ≃ₗ[E] S.V)
    (hm : m ∈ NLam Λ x) (hfr : ∀ a, frame F₂ a = n (m (frame x a))) : IsAdmissible Λ g F F₂ := by
  obtain ⟨ξ, hξl, hξd, hξm⟩ := hadm
  have hnΛ : ∀ y ∈ Λ, n y ∈ Λ := by
    intro y hy
    rw [← hn.1.2]
    exact Submodule.mem_map_of_mem hy
  obtain ⟨B, hBU, hBf, hBi⟩ := coef Λ g F hFz hFc n hn
  obtain ⟨A, hAU, hAf, hAi⟩ := coef Λ g x hxz hxc m hm
  let Ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E := ξ.map (fun t => (t : E))
  have hΞU : UT Ξ := ⟨fun a b h => by simp [Ξ, hξl a b h], fun a => by simp [Ξ, hξd a]⟩
  let M := B * (Ξ * A)
  have hMU : UT M := hBU.mul (hΞU.mul hAU)
  have hMi : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      ∀ a b, (haveI := P.isPrime; M a b ∈ locInt P.asIdeal) := by
    intro P hP
    haveI := P.isPrime
    exact mul_mem_locInt (hBi P hP) (mul_mem_locInt (fun a b => coe_mem_locInt _ (ξ a b)) (hAi P hP))
  have happ : ∀ a b, ∃ c : 𝓞 E, ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ w : 𝓞 E, (s : E) * ((c : E) - M a b) = ((g : 𝓞 E) : E) * w :=
    fun a b => approx _ _ (fun P hP => hMi P hP a b)
  choose c hc using happ
  let ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) :=
    fun a b => if b < a then 0 else if a = b then 1 else c a b
  refine ⟨ξ', fun a b h => by simp [ξ', h], fun a => by simp [ξ'], fun b P hP => ?_⟩
  haveI := P.isPrime
  let ε : Fin (r + 1) → S.V := fun a => frame x a - frE (frame F) Ξ a
  have hε : ∀ a, ε a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := fun a => hξm a P hP
  have hxε : frame x = fun a => frE (frame F) Ξ a + ε a := by
    funext a; simp [ε]
  have e1 : n (frE (frE (frame F) Ξ) A b) = frE (frame F) M b := by
    rw [frE_mul, frE_map, show (fun a => n (frame F a)) = frE (frame F) B from funext hBf, frE_mul]
  have key : frame F₂ b = frE (frame F) M b + n (frE ε A b) := by
    rw [hfr, hAf, hxε, frE_add, map_add (f := _), e1]
  have hdiff : frame F₂ b - frameAct (frame F) ξ' b =
      n (frE ε A b) + ∑ a, (M a b - (ξ' a b : E)) • frame F a := by
    rw [key]
    simp only [frE, frameAct, sub_smul, Finset.sum_sub_distrib]
    abel
  show frame F₂ b - frameAct (frame F) ξ' b ∈ _
  rw [hdiff]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun a _ => ?_)
  · refine localization_map₂ n (gsmul_map n hnΛ) ?_
    exact Submodule.sum_mem _ fun a _ => smul_mem_locP (hAi P hP a b) (hε a)
  · rcases lt_trichotomy a b with h | rfl | h
    · have hξ' : ξ' a b = c a b := by simp [ξ', not_lt.mpr h.le, h.ne]
      obtain ⟨s, hs, w, hw⟩ := hc a b P hP
      rw [hξ']
      refine gsmem (w := -w) hs ?_ (frame_mem_locP Λ g F hFz hFc P hP a)
      push_cast at hw ⊢
      linear_combination -hw
    · simp [ξ', hMU.2 a]
    · simp [ξ', h, hMU.1 a b h]

end Gen

end PI.TCS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.MemSpanImageEquiv
section
noncomputable section

open scoped Classical

namespace PI.TCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def Tr (γ : S.V ≃ₗ[E] S.V) (A₂ A : Submodule (𝓞 E) S.V) : Prop := ∀ v, v ∈ A₂ ↔ γ.symm v ∈ A

def TrE (γ : S.V ≃ₗ[E] S.V) (U₂ U : Submodule E S.V) : Prop := ∀ v, v ∈ U₂ ↔ γ.symm v ∈ U

variable {γ : S.V ≃ₗ[E] S.V}

theorem Tr.inf {A₂ A B₂ B : Submodule (𝓞 E) S.V} (hA : Tr γ A₂ A) (hB : Tr γ B₂ B) :
    Tr γ (A₂ ⊓ B₂) (A ⊓ B) := by
  intro v
  rw [Submodule.mem_inf, Submodule.mem_inf, hA v, hB v]

theorem Tr.sup {A₂ A B₂ B : Submodule (𝓞 E) S.V} (hA : Tr γ A₂ A) (hB : Tr γ B₂ B) :
    Tr γ (A₂ ⊔ B₂) (A ⊔ B) := by
  intro v
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨γ.symm y, (hA y).1 hy, γ.symm z, (hB z).1 hz, (map_add _ _ _).symm⟩
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨γ y, (hA _).2 (by simpa using hy), γ z, (hB _).2 (by simpa using hz), ?_⟩
    rw [← map_add (f := _), hyz, LinearEquiv.apply_symm_apply]

theorem TrE.toO {U₂ U : Submodule E S.V} (h : TrE γ U₂ U) : Tr γ (toO S U₂) (toO S U) := by
  intro v
  exact h v

theorem Tr.localization₂ {p : Ideal (𝓞 E)} [p.IsPrime] {A₂ A : Submodule (𝓞 E) S.V} (h : Tr γ A₂ A) :
    Tr γ (Formalism.HermitianLatticesTheory.localization₂ p A₂) (Formalism.HermitianLatticesTheory.localization₂ p A) := by
  intro v
  rw [mem_locP, mem_locP]
  refine exists_congr (fun s => and_congr_right (fun _ => ?_))
  rw [h, lin_osmul]

theorem Tr.eq {A₂ A B₂ B : Submodule (𝓞 E) S.V} (hA : Tr γ A₂ A) (hB : Tr γ B₂ B) (h : A = B) :
    A₂ = B₂ := by
  ext v
  rw [hA, hB, h]

theorem mem_span_image_equiv {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (β : M ≃ₗ[R] M)
    (s : Set M) (v : M) : v ∈ Submodule.span R (β '' s) ↔ β.symm v ∈ Submodule.span R s := by
  have hs : (β '' s) = (β : M →ₗ[R] M) '' s := rfl
  rw [hs, Submodule.span_image, Submodule.mem_map_equiv]

theorem Tr.span {s₂ s : Set S.V} (h : s₂ = γ '' s) : Tr γ (Submodule.span (𝓞 E) s₂) (Submodule.span (𝓞 E) s) := by
  subst h
  intro v
  exact mem_span_image_equiv (γ.restrictScalars (𝓞 E)) s v

theorem TrE.span {s₂ s : Set S.V} (h : s₂ = γ '' s) : TrE γ (Submodule.span E s₂) (Submodule.span E s) := by
  subst h
  intro v
  exact mem_span_image_equiv γ s v

theorem tr_of_gmap {Λ : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap γ Λ = Λ) : Tr γ Λ Λ := by
  intro v
  constructor
  · intro hv
    rw [← h] at hv
    unfold Formalism.HermitianLatticesTheory.gmap at hv
    rw [Submodule.mem_map] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    simpa using hy
  · intro hv
    rw [← h]
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.mem_map]
    exact ⟨γ.symm v, hv, by simp⟩

theorem TrE.perp {U₂ U : Submodule E S.V} (h : TrE γ U₂ U) (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) :
    TrE γ (Formalism.MainNotions.S.Lat.orth S U₂) (Formalism.MainNotions.S.Lat.orth S U) := by
  intro v
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv y hy
    have hgy : γ y ∈ U₂ := (h _).2 (by simpa using hy)
    rw [← hiso y (γ.symm v), LinearEquiv.apply_symm_apply]
    exact hv _ hgy
  · intro hv y hy
    have h1 := hv _ ((h y).1 hy)
    rw [← hiso, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    exact h1

variable {T' : E} {x F₂ : LFlag S r T'}

theorem trE_Xsp (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) : TrE γ (Xsp F₂) (Xsp x) := by
  have hs : Set.range F₂.fl.e = γ '' Set.range x.fl.e := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext he)
  exact TrE.span hs

theorem tr_XLam (Λ : Submodule (𝓞 E) S.V) (hΛ : Tr γ Λ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) :
    Tr γ (XLam Λ F₂) (XLam Λ x) := by
  unfold XLam
  exact Tr.inf hΛ (TrE.toO (trE_Xsp he))

theorem tr_Lsub (Λ : Submodule (𝓞 E) S.V) (hΛ : Tr γ Λ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k))
    (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) : Tr γ (Lsub Λ F₂) (Lsub Λ x) := by
  have hX := trE_Xsp he
  have hO := TrE.toO (TrE.perp hX hiso)
  unfold Lsub Lrep
  exact Tr.inf (Tr.sup (Tr.inf hΛ hO) (TrE.toO hX)) hO

theorem isLift_tr (Λ : Submodule (𝓞 E) S.V) (hΛ : Tr γ Λ Λ) (hz : F₂.fl.z = γ x.fl.z)
    (hzt : F₂.zt = γ x.zt) (hx : IsLift Λ x) : IsLift Λ F₂ := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [hz]
    exact (hΛ _).2 (by simpa using h1)
  · rw [hzt, hz, h2]

theorem fixedConv_tr (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hΛ : Tr γ Λ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k))
    (hz : F₂.fl.z = γ x.fl.z) (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) (hx : IsFixedConv Λ g x) :
    IsFixedConv Λ g F₂ := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun P => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc0, hc1, hloc⟩ := h1 P
    refine ⟨c, hc0, hc1, ?_⟩
    haveI := P.isPrime
    have hs : Set.range (fun a => c a • F₂.fl.e a) = γ '' Set.range (fun a => c a • x.fl.e a) := by
      rw [← Set.range_comp]
      congr 1
      funext a
      simp [he a]
    exact Tr.eq (Tr.localization₂ (tr_XLam Λ hΛ he)) (Tr.localization₂ (Tr.span hs)) hloc
  · apply h2 c
    have h3 := (tr_Lsub Λ hΛ he hiso (c • F₂.fl.z)).1 hc
    rw [hz, map_smul, LinearEquiv.symm_apply_apply] at h3
    exact h3

end Gen

end PI.TCS
end
end

