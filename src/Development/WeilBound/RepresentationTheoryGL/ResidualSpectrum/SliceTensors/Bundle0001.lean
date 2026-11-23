module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsNeZeroOfISup
section
noncomputable section

open scoped MonoidAlgebra

namespace PositivityTheory.Rg.Rs.PLsAbs2

theorem exists_ne_zero_of_iSup {R M S : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S]
    [Module R S] [IsSimpleModule R S] {ι : Type} (fs : ι → S →ₗ[R] M)
    (htop : ⨆ i, LinearMap.range (fs i) = ⊤) (x : M) (hx : x ≠ 0) : ∃ p : M →ₗ[R] S, p x ≠ 0 := by
  have : IsSemisimpleModule R M := isSemisimpleModule_of_isSemisimpleModule_submodule'
    (fun i => IsSemisimpleModule.of_surjective (fs i).rangeRestrict (fs i).surjective_rangeRestrict) htop
  rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (Submodule.span R {x}) with hC | ⟨A, hAC, hA⟩
  · exact absurd ((Submodule.span_singleton_eq_bot).1 hC) hx
  obtain ⟨h, hh⟩ := IsSemisimpleModule.extension_property A.subtype A.injective_subtype LinearMap.id
  have := hA
  have hA0 : A ≠ ⊥ := ((isSimpleModule_iff_isAtom).1 hA).1
  have hhx : h x ≠ 0 := by
    intro h0
    apply hA0
    have hle : Submodule.span R {x} ≤ LinearMap.ker h := (Submodule.span_singleton_le_iff_mem _ _).2 h0
    refine eq_bot_iff.2 fun a ha => ?_
    have e1 : h a = ⟨a, ha⟩ := LinearMap.congr_fun hh ⟨a, ha⟩
    have e2 : h a = 0 := LinearMap.mem_ker.1 (hle (hAC ha))
    have e3 : (⟨a, ha⟩ : A) = 0 := e1.symm.trans e2
    exact (Submodule.mem_bot R).2 (congrArg Subtype.val e3)
  obtain ⟨i, hi⟩ : ∃ i, h ∘ₗ fs i ≠ 0 := by
    by_contra hc
    push Not at hc
    have hle : (⨆ i, LinearMap.range (fs i)) ≤ LinearMap.ker h := iSup_le fun i => by
      rintro _ ⟨v, rfl⟩
      exact LinearMap.congr_fun (hc i) v
    rw [htop] at hle
    exact hhx (hle Submodule.mem_top)
  let e := LinearEquiv.ofBijective (h ∘ₗ fs i) (LinearMap.bijective_of_ne_zero hi)
  exact ⟨e.symm.toLinearMap ∘ₗ h, fun h0 => hhx (by simpa using congrArg e h0)⟩

theorem exists_proj {Γ M X : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X]
    (σ : Γ → M →ₗ[ℂ] M) (ρ : Representation ℂ Γ X) (hρ : ρ.IsIrreducible) {ι : Type} (Φ : ι → X →ₗ[ℂ] M)
    (hΦ : ∀ i g v, Φ i (ρ g v) = σ g (Φ i v)) {t : M} (ht : t ∈ ⨆ i, LinearMap.range (Φ i)) (h0 : t ≠ 0) :
    ∃ p : M →ₗ[ℂ] X, p t ≠ 0 ∧ ∀ g, ∀ s ∈ ⨆ i, LinearMap.range (Φ i), p (σ g s) = ρ g (p s) := by
  classical
  set T := ⨆ i, LinearMap.range (Φ i) with hTdef
  have hmemΦ : ∀ i v, Φ i v ∈ T := fun i v => Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (Φ i) v)
  have hgen : ∀ f₁ f₂ : M →ₗ[ℂ] M, (∀ i v, f₁ (Φ i v) = f₂ (Φ i v)) → ∀ s ∈ T, f₁ s = f₂ s := by
    intro f₁ f₂ h s hs
    have hle : T ≤ LinearMap.ker (f₁ - f₂) := iSup_le fun i => by
      rintro _ ⟨v, rfl⟩
      simp [h i v]
    have := hle hs
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  have hT : ∀ g, ∀ s ∈ T, σ g s ∈ T := by
    intro g s hs
    have hle : T ≤ T.comap (σ g) := iSup_le fun i => by
      rintro _ ⟨v, rfl⟩
      show σ g (Φ i v) ∈ T
      rw [← hΦ]
      exact hmemΦ i _
    exact hle hs
  let τ : Representation ℂ Γ T :=
    { toFun := fun g => (σ g).restrict (hT g)
      map_one' := LinearMap.ext fun s => Subtype.ext (by
        show σ 1 s.1 = s.1
        exact hgen (σ 1) LinearMap.id (fun i v => by rw [← hΦ, map_one]; rfl) s.1 s.2)
      map_mul' := fun g h => LinearMap.ext fun s => Subtype.ext (by
        show σ (g * h) s.1 = σ g (σ h s.1)
        exact hgen (σ (g * h)) (σ g ∘ₗ σ h) (fun i v => by
          rw [LinearMap.comp_apply, ← hΦ i h v, ← hΦ i g, ← hΦ i (g * h), map_mul, Module.End.mul_apply]) s.1 s.2) }
  let Ψ : ι → Representation.IntertwiningMap ρ τ := fun i =>
    ((Φ i).codRestrict T (hmemΦ i)).intertwiningMap_of_isIntertwiningMap ρ τ (fun g v => Subtype.ext (hΦ i g v))
  let A := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ
  have : IsSimpleModule ℂ[Γ] ρ.asModule := (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  have hN : ∀ y ∈ T, ∃ hy : y ∈ T, (show τ.asModule from ⟨y, hy⟩) ∈ ⨆ i, LinearMap.range (A (Ψ i)) :=
    fun y hy => Submodule.iSup_induction (fun i => LinearMap.range (Φ i))
      (motive := fun y => ∃ hy : y ∈ T, (show τ.asModule from ⟨y, hy⟩) ∈ ⨆ i, LinearMap.range (A (Ψ i))) hy
      (fun i x hx => by
        obtain ⟨v, rfl⟩ := hx
        exact ⟨hmemΦ i v, Submodule.mem_iSup_of_mem i (LinearMap.mem_range.2 ⟨v, rfl⟩)⟩)
      ⟨T.zero_mem, Submodule.zero_mem _⟩
      (fun _ _ ⟨ha, h1⟩ ⟨hb, h2⟩ => ⟨T.add_mem ha hb, Submodule.add_mem _ h1 h2⟩)
  have htop : ⨆ i, LinearMap.range (A (Ψ i)) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨_, hx⟩ := hN (x : T).1 (x : T).2
    exact hx
  obtain ⟨q, hq⟩ := exists_ne_zero_of_iSup (fun i => A (Ψ i)) htop (show τ.asModule from ⟨t, ht⟩)
    (fun e => h0 (congrArg (fun y : T => y.1) e))
  let qI := (Representation.IntertwiningMap.equivLinearMapAsModule τ ρ).symm q
  obtain ⟨p, hp⟩ := LinearMap.exists_extend qI.toLinearMap
  have hpv : ∀ s (hs : s ∈ T), p s = qI.toLinearMap ⟨s, hs⟩ := fun s hs => LinearMap.congr_fun hp ⟨s, hs⟩
  refine ⟨p, ?_, fun g s hs => ?_⟩
  · rw [hpv t ht]
    exact hq
  · rw [hpv _ (hT g s hs), hpv s hs]
    exact LinearMap.congr_fun (qI.isIntertwining' g) ⟨s, hs⟩

end PositivityTheory.Rg.Rs.PLsAbs2

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceC
section
noncomputable section

namespace PositivityTheory.Rg.Rs.SliceClasses

section Fixed

variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*}

theorem C_pow_mem {P : Submodule ℂ U} {f : Module.End ℂ U} (hf : ∀ v ∈ P, f v ∈ P) :
    ∀ k : ℕ, ∀ v ∈ P, (f ^ k) v ∈ P := by
  intro k
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih => intro v hv; rw [pow_succ', Module.End.mul_apply]; exact hf _ (ih v hv)

theorem C_sub_one_mem {P : Submodule ℂ U} {f : Module.End ℂ U} (hf : ∀ v ∈ P, f v ∈ P) :
    ∀ v ∈ P, (f - 1) v ∈ P := fun v hv => by
  rw [LinearMap.sub_apply, Module.End.one_apply]; exact P.sub_mem (hf v hv) hv

theorem C_comm_pow {M : ι → Module.End ℂ U} (hc : ∀ i j, Commute (M i) (M j)) (i j : ι) (k : ℕ) (x : U) :
    M j (((M i - 1) ^ k) x) = ((M i - 1) ^ k) (M j x) := by
  have h : Commute (M j) ((M i - 1) ^ k) := ((hc j i).sub_right (Commute.one_right _)).pow_right k
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply]

theorem C_nil (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) :
    ∀ (n : ℕ) (P : Submodule ℂ U), Module.finrank ℂ P = n → P ≠ ⊥ → (∀ i, ∀ v ∈ P, M i v ∈ P) →
      (∀ i, ∀ v ∈ P, ∃ k : ℕ, ((M i - 1) ^ k) v = 0) → ∃ w ∈ P, w ≠ 0 ∧ ∀ i, M i w = w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP hst hnil
  by_cases hall : ∀ i, ∀ v ∈ P, M i v = v
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    exact ⟨v, hv, hv0, fun i => hall i v hv⟩
  push Not at hall
  obtain ⟨i, v, hv, hMv⟩ := hall
  classical
  set P' : Submodule ℂ U := P ⊓ LinearMap.ker (M i - 1) with hP'def
  have hlt : P' < P := by
    refine lt_of_le_of_ne inf_le_left fun h => hMv ?_
    have h2 : v ∈ P' := h ▸ hv
    have h3 := (Submodule.mem_inf.1 h2).2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h3
    exact h3
  have hne : P' ≠ ⊥ := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hex : ∃ k, (((M i - 1) ^ k : Module.End ℂ U)) u = 0 := hnil i u hu
    have hkk : ((M i - 1) ^ Nat.find hex) u = 0 := Nat.find_spec hex
    have hkk0 : Nat.find hex ≠ 0 := by
      intro h0; rw [h0, pow_zero, Module.End.one_apply] at hkk; exact hu0 hkk
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hkk0
    have hmin : ((M i - 1) ^ j) u ≠ 0 := Nat.find_min hex (by omega)
    refine (Submodule.ne_bot_iff _).2 ⟨((M i - 1) ^ j) u, Submodule.mem_inf.2 ⟨?_, ?_⟩, hmin⟩
    · exact C_pow_mem (C_sub_one_mem (hst i)) j u hu
    · rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', show j + 1 = Nat.find hex by omega]; exact hkk
  have hst' : ∀ l, ∀ x ∈ P', M l x ∈ P' := by
    intro l x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨hst l x hx1, ?_⟩
    rw [LinearMap.mem_ker] at hx2 ⊢
    have := C_comm_pow hc i l 1 x
    rw [pow_one] at this
    rw [← this, hx2, map_zero]
  have hnil' : ∀ l, ∀ x ∈ P', ∃ k : ℕ, ((M l - 1) ^ k) x = 0 := fun l x hx =>
    hnil l x (Submodule.mem_inf.1 hx).1
  obtain ⟨w, hw, hw0, hfix⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) P' rfl hne hst' hnil'
  exact ⟨w, (Submodule.mem_inf.1 hw).1, hw0, hfix⟩

theorem C_restrict_pow {P : Submodule ℂ U} {f : Module.End ℂ U} (hf : ∀ v ∈ P, f v ∈ P) :
    ∀ (m : ℕ) (x : P), (((f.restrict hf) ^ m) x : U) = (f ^ m) (x : U) := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih => intro x; rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ',
      Module.End.mul_apply]

theorem C_gen (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) (Φ : U →ₗ[ℂ] ℂ) :
    ∀ (n : ℕ) (P : Submodule ℂ U), Module.finrank ℂ P = n → (∀ i, ∀ v ∈ P, M i v ∈ P) →
      (∀ i, ∀ v ∈ P, Φ (M i v) = Φ v) → (∃ v ∈ P, Φ v ≠ 0) → ∃ w ∈ P, w ≠ 0 ∧ ∀ i, M i w = w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hst hinv hv
  obtain ⟨v, hv, hΦv⟩ := hv
  by_cases hnil : ∀ i, ∀ u ∈ P, ∃ k : ℕ, ((M i - 1) ^ k) u = 0
  · refine C_nil M hc _ P rfl ?_ hst hnil
    rintro rfl
    rw [Submodule.mem_bot] at hv
    exact hΦv (by rw [hv, map_zero])
  push Not at hnil
  obtain ⟨i, u, hu, hku⟩ := hnil
  have hgP : ∀ x ∈ P, (M i - 1) x ∈ P := C_sub_one_mem (hst i)
  obtain ⟨m, hm, hm1⟩ := ((LinearMap.eventually_isCompl_ker_pow_range_pow ((M i - 1).restrict hgP)).and
    (Filter.eventually_ge_atTop 1)).exists
  set Q : Submodule ℂ U := P ⊓ LinearMap.ker ((M i - 1) ^ m) with hQdef
  obtain ⟨k, hk, r, hr, hkr⟩ := Submodule.mem_sup.1 (hm.sup_eq_top ▸ Submodule.mem_top (x := (⟨v, hv⟩ : P)))
  have hΦr : Φ (r : U) = 0 := by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hr
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm1
    rw [← hy, C_restrict_pow hgP, add_comm, pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, hinv i _ (C_pow_mem hgP m' _ y.2), sub_self]
  have hkv : (k : U) + r = v := congrArg Subtype.val hkr
  have hΦk : Φ (k : U) ≠ 0 := by
    intro h0; apply hΦv; rw [← hkv, map_add (f := _), h0, hΦr, add_zero]
  have hkQ : (k : U) ∈ Q := by
    refine Submodule.mem_inf.2 ⟨k.2, ?_⟩
    rw [LinearMap.mem_ker, ← C_restrict_pow hgP, LinearMap.mem_ker.1 hk, Submodule.coe_zero]
  have hlt : Q < P := by
    refine lt_of_le_of_ne inf_le_left fun h => hku m ?_
    have h2 : u ∈ Q := h ▸ hu
    exact (Submodule.mem_inf.1 h2).2
  have hstQ : ∀ l, ∀ x ∈ Q, M l x ∈ Q := by
    intro l x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨hst l x hx1, ?_⟩
    rw [LinearMap.mem_ker] at hx2 ⊢
    rw [← C_comm_pow hc i l m x, hx2, map_zero]
  obtain ⟨w, hw, hw0, hfix⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) Q rfl hstQ
    (fun l x hx => hinv l x (Submodule.mem_inf.1 hx).1) ⟨k, hkQ, hΦk⟩
  exact ⟨w, (Submodule.mem_inf.1 hw).1, hw0, hfix⟩

end Fixed

theorem eig_lift {X Y : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W]
    (L : ℝ → (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hL : ∀ s t, ∀ w ∈ W, L s (L t w) = L t (L s w))
    (hW : ∀ t, ∀ w ∈ W, L t w ∈ W) (L' : ℝ → (Y → ℂ) →ₗ[ℂ] (Y → ℂ)) (B : (X → ℂ) → (Y → ℂ))
    (hadd : ∀ v ∈ W, ∀ w ∈ W, B (v + w) = B v + B w) (hsmul : ∀ (a : ℂ), ∀ w ∈ W, B (a • w) = a • B w)
    (c d : ℂ) (hB : ∀ t : ℝ, ∀ w ∈ W, B (L t w) = Complex.exp (d * t) • L' t (B w))
    (w₀ : X → ℂ) (hw₀ : w₀ ∈ W) (hne : B w₀ ≠ 0) (heig : ∀ t : ℝ, L' t (B w₀) = Complex.exp (c * t) • B w₀) :
    ∃ F ∈ W, F ≠ 0 ∧ ∀ t : ℝ, L t F = Complex.exp ((c + d) * t) • F := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, B w₀ y ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  let M : ℝ → Module.End ℂ W := fun t => Complex.exp (-((c + d) * t)) • (L t).restrict (hW t)
  have hMv : ∀ t (w : W), ((M t w : W) : X → ℂ) = Complex.exp (-((c + d) * t)) • L t (w : X → ℂ) := fun _ _ => rfl
  let Φ : W →ₗ[ℂ] ℂ :=
    { toFun := fun w => B (w : X → ℂ) y₀ / B w₀ y₀
      map_add' := fun v w => by
        simp only [Submodule.coe_add]
        rw [hadd _ v.2 _ w.2, Pi.add_apply, add_div]
      map_smul' := fun a w => by
        simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
        rw [hsmul a _ w.2, Pi.smul_apply, smul_eq_mul, mul_div_assoc] }
  have hΦ : ∀ w : W, Φ w = B (w : X → ℂ) y₀ / B w₀ y₀ := fun _ => rfl
  let P : Submodule ℂ W :=
    { carrier := {w | ∃ a : ℂ, B (w : X → ℂ) = a • B w₀}
      add_mem' := fun {v w} hv hw => by
        obtain ⟨a, ha⟩ := hv; obtain ⟨b, hb⟩ := hw
        exact ⟨a + b, by simp only [Submodule.coe_add]; rw [hadd _ v.2 _ w.2, ha, hb, add_smul]⟩
      zero_mem' := ⟨0, by
        have := hsmul 0 w₀ hw₀
        simpa using this⟩
      smul_mem' := fun a w hw => by
        obtain ⟨b, hb⟩ := hw
        exact ⟨a * b, by simp only [Submodule.coe_smul]; rw [hsmul a _ w.2, hb, smul_smul]⟩ }
  have hBM : ∀ t (w : W), B ((M t w : W) : X → ℂ) = Complex.exp (-(c * t)) • L' t (B (w : X → ℂ)) := by
    intro t w
    rw [hMv, hsmul _ _ (hW t _ w.2), hB t _ w.2, smul_smul, ← Complex.exp_add]
    congr 2
    ring
  have hPM : ∀ t (w : W) (a : ℂ), B (w : X → ℂ) = a • B w₀ → B ((M t w : W) : X → ℂ) = a • B w₀ := by
    intro t w a ha
    rw [hBM, ha, map_smul, heig, smul_smul, smul_smul]
    congr 1
    rw [mul_comm _ a, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hc : ∀ s t, Commute (M s) (M t) := by
    intro s t
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp only [Module.End.mul_apply]
    rw [hMv, hMv, hMv, hMv, map_smul, map_smul, hL s t _ w.2, smul_smul, smul_smul, mul_comm]
  obtain ⟨w, -, hw0, hfix⟩ := C_gen M hc Φ _ P rfl
    (fun t w hw => by obtain ⟨a, ha⟩ := hw; exact ⟨a, hPM t w a ha⟩)
    (fun t w hw => by obtain ⟨a, ha⟩ := hw; rw [hΦ, hΦ, hPM t w a ha, ha])
    ⟨⟨w₀, hw₀⟩, ⟨1, by rw [one_smul]⟩, by rw [hΦ]; exact div_ne_zero hy₀ hy₀⟩
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h), fun t => ?_⟩
  have h1 := congrArg Subtype.val (hfix t)
  rw [hMv] at h1
  calc L t (w : X → ℂ) = Complex.exp ((c + d) * t) • (Complex.exp (-((c + d) * t)) • L t (w : X → ℂ)) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp ((c + d) * t) • (w : X → ℂ) := by rw [h1]

end PositivityTheory.Rg.Rs.SliceClasses

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepA
section
namespace PositivityTheory.Rg.Rs.StrStepA

theorem adjacent (c₁ c₂ : ℝ) (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (S : Set ℝ)
    (hS : ∀ x, x ∈ S ↔ (∃ i : ℕ, i < d₁ ∧ x = c₁ + ((d₁ : ℝ) - 1) / 2 - i) ∨
      ∃ j : ℕ, j < d₂ ∧ x = c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hdisj : ∀ i j : ℕ, i < d₁ → j < d₂ → c₁ + ((d₁ : ℝ) - 1) / 2 - i ≠ c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n)
    (hneg : ∀ x ∈ S, -x ∈ S) (hP : ∀ u ∈ S, 1 ≤ u → u - 1 ∈ S) (hc : c₁ < c₂) :
    c₂ - c₁ = ((d₁ : ℝ) + d₂) / 2 := by
  set e₁ : ℝ := ((d₁ : ℝ) - 1) / 2 with he₁
  set e₂ : ℝ := ((d₂ : ℝ) - 1) / 2 with he₂
  have hd₁' : (1 : ℝ) ≤ d₁ := by exact_mod_cast hd₁
  have hd₂' : (1 : ℝ) ≤ d₂ := by exact_mod_cast hd₂
  have he₁0 : 0 ≤ e₁ := by rw [he₁]; linarith
  have he₂0 : 0 ≤ e₂ := by rw [he₂]; linarith
  have hcast₁ : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1 := by rw [Nat.cast_sub hd₁]; simp
  have hcast₂ : ((d₂ - 1 : ℕ) : ℝ) = d₂ - 1 := by rw [Nat.cast_sub hd₂]; simp
  set B : ℝ := c₁ + e₁ with hBdef
  set C : ℝ := c₂ + e₂ - ((d₂ : ℝ) - 1) with hCdef
  have hB : B ∈ S := (hS _).2 (Or.inl ⟨0, hd₁, by simp [hBdef]⟩)
  have hC : C ∈ S := (hS _).2 (Or.inr ⟨d₂ - 1, by omega, by rw [hcast₂]⟩)
  have hmem : ∀ x ∈ S, x ≤ B ∨ C ≤ x := by
    intro x hx
    rcases (hS x).1 hx with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · left; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
    · right
      have h1 : j ≤ d₂ - 1 := by omega
      have h2 : (j : ℝ) ≤ ((d₂ - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [hcast₂] at h2; linarith
  obtain ⟨n, hn⟩ := hint _ hC _ hB
  rcases lt_trichotomy n 1 with h | h | h
  · exfalso
    have hn0 : n ≤ 0 := by omega
    have hn0' : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    by_cases hCA : c₁ - e₁ ≤ C
    · have hk : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      have hk' : (((-n).toNat : ℕ) : ℝ) = -(n : ℝ) := by exact_mod_cast hk
      have hkd : (-n).toNat < d₁ := by
        have : (((-n).toNat : ℕ) : ℝ) < d₁ := by rw [hk']; linarith
        exact_mod_cast this
      refine hdisj (-n).toNat (d₂ - 1) hkd (by omega) ?_
      rw [hk', hcast₂]; linarith
    · rw [not_le] at hCA
      have hJ0 : (0 : ℤ) ≤ n + d₁ + d₂ - 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) + d₁ + d₂ - 2 := by linarith
        exact_mod_cast this
      have hJ1 : n + d₁ + d₂ - 2 < (d₂ : ℤ) := by
        have : (n : ℝ) + d₁ + d₂ - 2 < d₂ := by linarith
        exact_mod_cast this
      have hj : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℤ) = n + d₁ + d₂ - 2 := Int.toNat_of_nonneg hJ0
      have hj' : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℝ) = (n : ℝ) + d₁ + d₂ - 2 := by exact_mod_cast hj
      have hjd : (n + d₁ + d₂ - 2).toNat < d₂ := by omega
      refine hdisj (d₁ - 1) (n + d₁ + d₂ - 2).toNat (by omega) hjd ?_
      rw [hj', hcast₁]; linarith
  · subst h
    push_cast at hn
    linarith
  · exfalso
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
    have hC1 : C - 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hB1 : B + 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hClt : C < 1 := by
      by_contra h3; exact hC1 (hP _ hC (not_lt.1 h3))
    have hBgt : -1 < B := by
      by_contra h3; rw [not_lt] at h3
      have h4 := hneg _ (hP _ (hneg _ hB) (by linarith))
      exact hB1 (by convert h4 using 1; ring)
    linarith

end PositivityTheory.Rg.Rs.StrStepA
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.SdNormCpow
section
namespace PositivityTheory.Rg.Rs.StrStepA

theorem sd_norm_cpow (q : ℕ) (hq : 1 < q) (x : ℝ) : ‖(q : ℂ) ^ (-(x : ℂ))‖ = (q : ℝ) ^ (-x) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem step_down (q : ℕ) (hq : 1 < q) (B₀ : Multiset ℂ)
    (hB : ∀ β ∈ B₀, (q : ℝ) ^ (-(1 / 2) : ℝ) < ‖β‖ ∧ ‖β‖ < (q : ℝ) ^ (1 / 2 : ℝ)) {α : ℂ} (hα : α ∈ B₀)
    (S : Set ℝ) (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n) (M : Multiset ℂ)
    (hM : ∀ z, z ∈ M ↔ ∃ x ∈ S, ∃ β ∈ B₀, z = β * (q : ℂ) ^ (-(x : ℂ)))
    (hgap : ∀ z : ℂ, ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) → M.count z ≤ M.count ((q : ℂ) * z))
    {u : ℝ} (hu : u ∈ S) (hu1 : 1 ≤ u) : u - 1 ∈ S := by
  have hQ : (1 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  set z : ℂ := α * (q : ℂ) ^ (-(u : ℂ)) with hz
  have hzM : z ∈ M := (hM z).2 ⟨u, hu, α, hα, rfl⟩
  have hnz : ‖z‖ = ‖α‖ * (q : ℝ) ^ (-u) := by rw [hz, norm_mul, sd_norm_cpow q hq]
  have hsmall : ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [hnz]
    have h1 : ‖α‖ * (q : ℝ) ^ (-u) < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-u) :=
      mul_lt_mul_of_pos_right (hB α hα).2 (Real.rpow_pos_of_pos hQ0 _)
    have h2 : (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-u) = (q : ℝ) ^ (1 / 2 - u) := by
      rw [← Real.rpow_add hQ0]; ring_nf
    have h3 : (q : ℝ) ^ (1 / 2 - u) ≤ (q : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)
    linarith
  have hc1 : 0 < M.count z := Multiset.count_pos.2 hzM
  have hc2 : 0 < M.count ((q : ℂ) * z) := lt_of_lt_of_le hc1 (hgap z hsmall)
  obtain ⟨x, hx, β, hβ, e⟩ := (hM _).1 (Multiset.count_pos.1 hc2)
  have en : (q : ℝ) * (‖α‖ * (q : ℝ) ^ (-u)) = ‖β‖ * (q : ℝ) ^ (-x) := by
    have h := congrArg norm e
    rw [norm_mul, hnz, norm_mul, sd_norm_cpow q hq, Complex.norm_natCast] at h
    exact h
  have hβn : ‖β‖ = ‖α‖ * (q : ℝ) ^ (1 - u + x) := by
    have e1 : (q : ℝ) ^ (1 - u + x) = q * (q : ℝ) ^ (-u) * (q : ℝ) ^ x := by
      rw [Real.rpow_add hQ0, Real.rpow_sub hQ0, Real.rpow_one, Real.rpow_neg hQ0.le]
      field_simp
    have hxx : (q : ℝ) ^ (-x) * (q : ℝ) ^ x = 1 := by rw [← Real.rpow_add hQ0]; simp
    calc ‖β‖ = ‖β‖ * (q : ℝ) ^ (-x) * (q : ℝ) ^ x := by rw [mul_assoc, hxx, mul_one]
      _ = q * (‖α‖ * (q : ℝ) ^ (-u)) * (q : ℝ) ^ x := by rw [en]
      _ = ‖α‖ * (q : ℝ) ^ (1 - u + x) := by rw [e1]; ring
  obtain ⟨n, hn⟩ := hint x hx u hu
  have hk : 1 - u + x = ((n + 1 : ℤ) : ℝ) := by push_cast; linarith
  rw [hk, Real.rpow_intCast] at hβn
  obtain ⟨hb1, hb2⟩ := hB β hβ
  obtain ⟨ha1, ha2⟩ := hB α hα
  have hpos : (0 : ℝ) < (q : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hQ0 _
  have hhalf : (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) = (q : ℝ) ^ (1 / 2 : ℝ) := by
    have h := (Real.rpow_add hQ0 (-(1 / 2) : ℝ) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; norm_num
  rcases lt_trichotomy (n + 1) 0 with hneg | hzero | hposn
  ·
    exfalso
    have hle : (q : ℝ) ^ (n + 1) ≤ (q : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hQ.le (by omega)
    have hzp : (0 : ℝ) < (q : ℝ) ^ (n + 1) := zpow_pos hQ0 _
    have : ‖β‖ < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-1 : ℤ) := by
      rw [hβn]
      calc ‖α‖ * (q : ℝ) ^ (n + 1) < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_right ha2 hzp
        _ ≤ _ := mul_le_mul_of_nonneg_left hle (Real.rpow_pos_of_pos hQ0 _).le
    rw [← hhalf, zpow_neg_one, mul_assoc, mul_inv_cancel₀ hQ0.ne', mul_one] at this
    linarith
  · have hx' : x = u - 1 := by
      have : (n : ℝ) = -1 := by exact_mod_cast (by omega : n = -1)
      linarith
    rw [← hx']; exact hx
  · exfalso
    have hle : (q : ℝ) ^ (1 : ℤ) ≤ (q : ℝ) ^ (n + 1) := zpow_le_zpow_right₀ hQ.le (by omega)
    have : (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (1 : ℤ) < ‖β‖ := by
      rw [hβn]
      calc (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (1 : ℤ) ≤ (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (n + 1) :=
            mul_le_mul_of_nonneg_left hle hpos.le
        _ < ‖α‖ * (q : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_right ha1 (zpow_pos hQ0 _)
    rw [zpow_one, hhalf] at this
    linarith

end PositivityTheory.Rg.Rs.StrStepA
end

