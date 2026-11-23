module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChainMap
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'}

private theorem adj_map (j : R →+* R') (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext i i'
  simp only [adj_apply, Matrix.map_apply, map_zsmul]

private theorem conj_map (j : R →+* R') (n X : M4 R) :
    adj (n.map j) * X.map j * n.map j = (adj n * X * n).map j := by
  rw [adj_map, ← Matrix.map_mul, ← Matrix.map_mul]

private theorem map_inj (hj : Function.Injective j) {X Y : M4 R} : X.map j = Y.map j ↔ X = Y :=
  (Matrix.map_injective hj).eq_iff

private theorem isGSp_iff (hj : Function.Injective j) (ν : R) (X : M4 R) : IsGSp (j ν) (X.map j) ↔ IsGSp ν X := by
  have h : (j ν) • (1 : M4 R') = (ν • (1 : M4 R)).map j := by
    ext i i'
    by_cases h : i = i' <;> simp [Matrix.one_apply, h]
  unfold IsGSp
  rw [adj_map, ← Matrix.map_mul, h, map_inj hj]

private theorem one_iff (hj : Function.Injective j) (X : M4 R) : X.map j = 1 ↔ X = 1 := by
  rw [← Matrix.map_one (⇑j) (map_zero j) (map_one j), map_inj hj]

private theorem diag_iff (hj : Function.Injective j) (X : M4 R) : (X.map j).IsDiag ↔ X.IsDiag := by
  simp only [Matrix.IsDiag, Matrix.map_apply, map_eq_zero_iff j hj]

private theorem up_iff (hj : Function.Injective j) (X : M4 R) : IsUp (X.map j) ↔ IsUp X := by
  simp only [IsUp, Matrix.map_apply, map_eq_zero_iff j hj]

private theorem low_iff (hj : Function.Injective j) (X : M4 R) : IsLow (X.map j) ↔ IsLow X := by
  have h := isGSp_iff hj 1 X
  rw [map_one] at h
  simp only [IsLow, h, Matrix.map_apply, map_eq_zero_iff j hj, map_eq_one_iff j hj]

private theorem suppM_iff (hj : Function.Injective j) (S : Finset (ℤ × ℤ)) (X : M4 R) :
    SuppM S (X.map j) ↔ SuppM S X := by
  simp only [SuppM, Matrix.map_apply, map_eq_zero_iff j hj]

variable {ι Γ : Type} [Group Γ]

private theorem r_map (j : R →+* R') (c : PD ι Γ R) (g : Γ) : (c.map j).r g = (c.r g).map j := rfl

private theorem n_map (j : R →+* R') (c : PD ι Γ R) (v : ι) : (c.map j).n v = (c.n v).map j := rfl

private theorem psi_map (j : R →+* R') (c : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) :
    (c.map j).ψ v i s = j (c.ψ v i s) := by
  simp only [PD.ψ, r_map, n_map, conj_map, Matrix.map_apply]

private theorem supp_iff (hj : Function.Injective j) (S : Finset (ℤ × ℤ)) (c : PD ι Γ R) :
    Supp S (c.map j).r ↔ Supp S c.r := by
  simp only [Supp, r_map, suppM_iff hj]

private theorem ent_iff (hj : Function.Injective j) (c : PD ι Γ R) (w : ℤ × ℤ) :
    Ent (c.map j).r w ↔ Ent c.r w := by
  simp only [Ent, r_map, Matrix.map_apply, ne_eq, map_eq_zero_iff j hj]

private theorem adic_bot {X : Type} [TopologicalSpace X] (f : X → R) : AdicCont ⊥ f ↔ IsLocallyConstant f := by
  refine ⟨fun h => ?_, fun h N => h.comp _⟩
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]

private theorem cont_iff [TopologicalSpace Γ] (hj : Function.Injective j) (c : PD ι Γ R) :
    (c.map j).Cont ⊥ ↔ c.Cont ⊥ := by
  simp only [PD.Cont, adic_bot, r_map, Matrix.map_apply]
  exact forall_congr' fun a => forall_congr' fun b =>
    ⟨fun h => IsLocallyConstant.desc _ j h hj, fun h => h.comp j⟩

end

theorem UpperTheory.V.Ws.chainMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k k' : Type} [Field k] [Field k'] (a : O →+* k) (j : k →+* k') (c : PD Φ.ι Γ k),
      (Φ.IsRes (j.comp a) (c.map j) ↔ Φ.IsRes a c) ∧ (Φ.Good (j.comp a) (c.map j) ↔ Φ.Good a c) ∧ Function.Injective fun c : PD Φ.ι Γ k => c.map j := by
  intro O Γ _ _ _ _ _ _ Φ k k' _ _ a j c
  have hj : Function.Injective j := j.injective
  have e1 : ∀ g, IsGSp ((j.comp a) (Φ.ν g : O)) ((c.map j).r g) ↔ IsGSp (a (Φ.ν g)) (c.r g) :=
    fun g => by rw [RingHom.comp_apply, r_map, isGSp_iff hj]
  have e2 : ∀ g, (c.map j).r g = 1 ↔ c.r g = 1 := fun g => by rw [r_map, one_iff hj]
  have e3 : Matrix.IsDiag ((c.map j).r Φ.g0) ↔ Matrix.IsDiag (c.r Φ.g0) := by rw [r_map, diag_iff hj]
  have e4 : ∀ v, IsLow ((c.map j).n v) ↔ IsLow (c.n v) := fun v => by rw [n_map, low_iff hj]
  have e5 : ∀ v s, IsUp (adj ((c.map j).n v) * (c.map j).r s * (c.map j).n v) ↔
      IsUp (adj (c.n v) * c.r s * c.n v) :=
    fun v s => by rw [n_map, r_map, conj_map, up_iff hj]
  have e6 : ∀ v i s, (c.map j).ψ v i s = 1 ↔ c.ψ v i s = 1 :=
    fun v i s => by rw [psi_map, map_eq_one_iff j hj]
  have e7 : ∀ g i, (c.map j).r g i i = (j.comp a) (Φ.χ i g : O) ↔ c.r g i i = a (Φ.χ i g) :=
    fun g i => by rw [r_map, Matrix.map_apply, RingHom.comp_apply, hj.eq_iff]
  have e8 : ∀ v i s, (c.map j).ψ v i s = (j.comp a) (Φ.χ i s : O) ↔ c.ψ v i s = a (Φ.χ i s) :=
    fun v i s => by rw [psi_map, RingHom.comp_apply, hj.eq_iff]
  have e9 : ((Supp nP (c.map j).r ∧ ∀ v, SuppM qQ ((c.map j).n v)) ∨ Supp nM (c.map j).r) ↔
      ((Supp nP c.r ∧ ∀ v, SuppM qQ (c.n v)) ∨ Supp nM c.r) := by
    simp only [supp_iff hj, n_map, suppM_iff hj]
  have e10 : Fr.InV (Φ := Φ) (c.map j) ↔ Fr.InV (Φ := Φ) c := by
    simp only [Fr.InV, supp_iff hj, n_map, suppM_iff hj, Matrix.map_apply, ne_eq, map_eq_zero_iff j hj]
  have hP : Φ.IsPair (j.comp a) (c.map j) ↔ Φ.IsPair a c :=
    ⟨fun h => ⟨fun g => (e1 g).1 (h.mult g), fun g hg => (e2 g).1 (h.kill g hg), e3.1 h.nrm,
        fun v => (e4 v).1 (h.low v), fun v s hs => (e5 v s).1 (h.flag v s hs),
        fun v s hs i => (e6 v i s).1 (h.mu v s hs i)⟩,
      fun h => ⟨fun g => (e1 g).2 (h.mult g), fun g hg => (e2 g).2 (h.kill g hg), e3.2 h.nrm,
        fun v => (e4 v).2 (h.low v), fun v s hs => (e5 v s).2 (h.flag v s hs),
        fun v s hs i => (e6 v i s).2 (h.mu v s hs i)⟩⟩
  have hR : Φ.Res (j.comp a) (c.map j) ↔ Φ.Res a c :=
    ⟨fun h => ⟨fun g i => (e7 g i).1 (h.diag g i), fun v s hs i => (e8 v i s).1 (h.char v s hs i),
        e9.1 h.shape⟩,
      fun h => ⟨fun g i => (e7 g i).2 (h.diag g i), fun v s hs i => (e8 v i s).2 (h.char v s hs i),
        e9.2 h.shape⟩⟩
  refine ⟨⟨fun h => ⟨hP.1 h.pair, hR.1 h.res, (cont_iff hj c).1 h.cont⟩,
    fun h => ⟨hP.2 h.pair, hR.2 h.res, (cont_iff hj c).2 h.cont⟩⟩, ?_, ?_⟩
  · simp only [Fr.Good, ent_iff hj, e10, RingHom.comp_apply, ne_eq, map_eq_one_iff j hj]
  · intro x y h
    apply PD.ext
    · ext g : 1
      exact (map_inj hj).1 (congrArg (fun e : PD Φ.ι Γ k' => e.r g) h)
    · funext v
      exact (map_inj hj).1 (congrArg (fun e : PD Φ.ι Γ k' => e.n v) h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GlobalTheory
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.LineM

variable {k : Type} [Field k]

private def GlobalTheory (X : M4 k) : Prop := ∀ i j : Fin 4, (i.1 < 2 ∨ 2 ≤ j.1) → X i j = 0

private def Par (X : M4 k) : Prop := ∀ i j : Fin 4, i.1 < 2 → 2 ≤ j.1 → X i j = 0

private noncomputable def comb (A B : M4 k) : M4 k[X] := Matrix.of fun i j => C (A i j) + X * C (B i j - A i j)

private theorem comb_apply (A B : M4 k) (i j : Fin 4) : comb A B i j = C (A i j) + X * C (B i j - A i j) := rfl

private theorem comb_eq (A B : M4 k) : comb A B = A.map C + (X : k[X]) • (B - A).map C := by
  ext1 i j; simp [comb_apply]

private theorem blk_mul {A B : M4 k} (hA : GlobalTheory A) (hB : GlobalTheory B) : A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l.1 2 with h | h
  · rw [hB l j (Or.inl h), mul_zero]
  · rw [hA i l (Or.inr h), zero_mul]

private theorem blk_par {A B : M4 k} (hA : GlobalTheory A) (hB : Par B) : GlobalTheory (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases hij with h | h
  · rw [hA i l (Or.inl h), zero_mul]
  rcases lt_or_ge l.1 2 with h' | h'
  · rw [hB l j h' h, mul_zero]
  · rw [hA i l (Or.inr h'), zero_mul]

private theorem par_blk {A B : M4 k} (hA : Par A) (hB : GlobalTheory B) : GlobalTheory (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases hij with h | h
  · rcases lt_or_ge l.1 2 with h' | h'
    · rw [hB l j (Or.inl h'), mul_zero]
    · rw [hA i l h h', zero_mul]
  · rw [hB l j (Or.inr h), mul_zero]

private theorem blk_sub_mul {A B A' B' : M4 k} (hA : Par A) (hB' : Par B') (h : GlobalTheory (B - A)) (h' : GlobalTheory (B' - A')) :
    GlobalTheory (B * B' - A * A') := by
  have e : B * B' - A * A' = (B - A) * B' + A * (B' - A') := by noncomm_ring
  intro i j hij
  rw [e, Matrix.add_apply, blk_par h hB' i j hij, par_blk hA h' i j hij, add_zero]

private theorem comb_mul {A B A' B' : M4 k} (h : GlobalTheory (B - A)) (h' : GlobalTheory (B' - A')) :
    comb A B * comb A' B' = comb (A * A') (B * B') := by
  have h0 := blk_mul h h'
  have e : B * B' - A * A' = (B - A) * A' + A * (B' - A') + (B - A) * (B' - A') := by noncomm_ring
  rw [h0, add_zero] at e
  have h1 : ((B - A).map C : M4 k[X]) * (B' - A').map C = 0 := by
    rw [← Matrix.map_mul, h0]; ext1 i j; simp
  simp only [comb_eq]
  rw [e, Matrix.map_add _ (fun a b => map_add C a b), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h1, smul_zero, add_zero, smul_add]
  abel

private theorem adj_comb (A B : M4 k) : adj (comb A B) = comb (adj A) (adj B) := by
  ext1 i j
  simp only [adj_apply, comb_apply, zsmul_eq_mul, map_sub, map_mul, map_intCast]
  ring

private theorem blk_adj {A B : M4 k} (h : GlobalTheory (B - A)) : GlobalTheory (adj B - adj A) := by
  intro i j hij
  have := h j.rev i.rev (by simp only [Fin.val_rev]; omega)
  rw [Matrix.sub_apply] at this ⊢
  rw [adj_apply, adj_apply, ← smul_sub, this, smul_zero]

private theorem par_adj {A : M4 k} (h : Par A) : Par (adj A) := by
  intro i j hi hj
  rw [adj_apply, h j.rev i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega), smul_zero]

private theorem comb_same {A B : M4 k} {i j : Fin 4} {x : k} (hA : A i j = x) (hB : B i j = x) :
    comb A B i j = C x := by
  simp [comb_apply, hA, hB]

private theorem comb_gsp {A B : M4 k} {ν : k} (h : GlobalTheory (B - A)) (hA : IsGSp ν A) (hB : IsGSp ν B) :
    IsGSp (C ν) (comb A B) := by
  unfold IsGSp at *
  rw [adj_comb, comb_mul (blk_adj h) h, hA, hB]
  ext1 i j
  rw [comb_same rfl rfl]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem e32 {A : M4 k} {ν : k} (hA : IsGSp ν A) (lo : ∀ i j, i < j → A i j = 0) :
    A 3 2 * A 0 0 + A 2 2 * A 1 0 = 0 := by
  have := congrFun (congrFun hA 1) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, lo 1 2 (by decide), lo 0 2 (by decide)] using this

private theorem blk_of {A B : M4 k} {ν : k} (hA : IsGSp ν A) (hB : IsGSp ν B) (lA : ∀ i j, i < j → A i j = 0)
    (lB : ∀ i j, i < j → B i j = 0) (d : ∀ i, A i i = B i i) (d0 : A 0 0 ≠ 0) (e : A 1 0 = B 1 0) : GlobalTheory (B - A) := by
  have h32 : B 3 2 = A 3 2 := by
    have h1 := e32 hA lA
    have h2 := e32 hB lB
    rw [← d, ← d, ← e] at h2
    exact mul_right_cancel₀ d0 (by linear_combination h2 - h1)
  intro i j hij
  rw [Matrix.sub_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [lA i j h, lB i j h, sub_zero]
  · subst h; rw [d, sub_self]
  · have : (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by revert i j; decide
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e, sub_self]
    · rw [h32, sub_self]

private theorem low_of {A : M4 k} (h : SuppM nM A) : ∀ i j, i < j → A i j = 0 := fun i j hij =>
  h i j hij.ne (by revert i j; decide)

private theorem par_of {A : M4 k} (h : ∀ i j, i < j → A i j = 0) : Par A := fun i j hi hj =>
  h i j (by rw [Fin.lt_def]; omega)

private theorem lc_of {Γ : Type} [TopologicalSpace Γ] {f : Γ → k} (h : AdicCont (⊥ : Ideal k) f) :
    IsLocallyConstant f := by
  have h1 := h 1
  refine IsLocallyConstant.desc f _ h1 fun x y hxy => ?_
  rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot] at hxy
  exact sub_eq_zero.mp hxy

end UpperTheory.V.Ws.LineM

open UpperTheory.V.Ws.LineM in
theorem UpperTheory.V.Ws.lineM :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ c c' : PD Φ.ι Γ k, Φ.IsRes a c → Φ.IsRes a c' → Supp nM c.r → Supp nM c'.r → c.SameAl c' → Φ.Linked a c c' := by
  intro O Γ _ _ _ _ _ _ Φ k _ a _ c c' hc hc' hs hs' hal
  have lr := fun g => low_of (hs g)
  have lr' := fun g => low_of (hs' g)
  have br : ∀ g, GlobalTheory (c'.r g - c.r g) := fun g =>
    blk_of (hc.pair.mult g) (hc'.pair.mult g) (lr g) (lr' g)
      (fun i => by rw [hc.res.diag, hc'.res.diag])
      (by rw [hc.res.diag]; exact ((Φ.χ 0 g).isUnit.map a).ne_zero) (hal.1 g)
  have bn : ∀ v, GlobalTheory (c'.n v - c.n v) := fun v =>
    blk_of (hc.pair.low v).1 (hc'.pair.low v).1 (hc.pair.low v).2.2 (hc'.pair.low v).2.2
      (fun i => by rw [(hc.pair.low v).2.1, (hc'.pair.low v).2.1])
      (by rw [(hc.pair.low v).2.1]; exact one_ne_zero) (hal.2 v)
  let ρ : Γ →* M4 k[X] :=
    { toFun := fun g => comb (c.r g) (c'.r g)
      map_one' := by
        ext1 i j
        rw [map_one, map_one, comb_same rfl rfl]
        by_cases e : i = j <;> simp [Matrix.one_apply, e]
      map_mul' := fun g h => by rw [map_mul, map_mul, comb_mul (br g) (br h)] }
  let P : PD Φ.ι Γ k[X] := ⟨ρ, fun v => comb (c.n v) (c'.n v)⟩
  have Pr : ∀ g, P.r g = comb (c.r g) (c'.r g) := fun _ => rfl
  have Pn : ∀ v, P.n v = comb (c.n v) (c'.n v) := fun _ => rfl
  have conj : ∀ v s, adj (P.n v) * P.r s * P.n v =
      comb (adj (c.n v) * c.r s * c.n v) (adj (c'.n v) * c'.r s * c'.n v) := fun v s => by
    rw [Pr, Pn, adj_comb, comb_mul (blk_adj (bn v)) (br s),
      comb_mul (blk_sub_mul (par_adj (par_of (hc.pair.low v).2.2)) (par_of (lr' s)) (blk_adj (bn v)) (br s)) (bn v)]
  refine ⟨P, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, Or.inr ?_⟩, ?_⟩, ?_, ?_⟩
  · intro g
    exact comb_gsp (br g) (hc.pair.mult g) (hc'.pair.mult g)
  · intro g hg
    rw [Pr, hc.pair.kill g hg, hc'.pair.kill g hg]
    ext1 i j
    rw [comb_same rfl rfl]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  · intro i j hij
    rw [Pr, comb_same (hc.pair.nrm hij) (hc'.pair.nrm hij), map_zero]
  · intro v
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · have := comb_gsp (bn v) (hc.pair.low v).1 (hc'.pair.low v).1
      rwa [map_one] at this
    · rw [Pn, comb_same ((hc.pair.low v).2.1 i) ((hc'.pair.low v).2.1 i), map_one]
    · rw [Pn, comb_same ((hc.pair.low v).2.2 i j hij) ((hc'.pair.low v).2.2 i j hij), map_zero]
  · intro v s hs i j hij
    rw [conj, comb_same (hc.pair.flag v s hs i j hij) (hc'.pair.flag v s hs i j hij), map_zero]
  · intro v s hs i
    unfold PD.ψ
    rw [conj, comb_same (hc.pair.mu v s hs i) (hc'.pair.mu v s hs i), map_one]
  · intro g i
    rw [Pr, comb_same (hc.res.diag g i) (hc'.res.diag g i)]; rfl
  · intro v s hs i
    unfold PD.ψ
    rw [conj, comb_same (hc.res.char v s hs i) (hc'.res.char v s hs i)]; rfl
  · intro g i j hij hw
    rw [Pr, comb_same (hs g i j hij hw) (hs' g i j hij hw), map_zero]
  · intro i j N
    exact ((lc_of (hc.cont i j)).prodMk (lc_of (hc'.cont i j))).comp
      fun x : k × k => Ideal.Quotient.mk ((⊥ : Ideal k[X]) ^ N) (C x.1 + X * C (x.2 - x.1))
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, Pr, comb_apply]
    · funext v; ext i j
      simp [PD.map, Pn, comb_apply]
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, Pr, comb_apply]
    · funext v; ext i j
      simp [PD.map, Pn, comb_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PureDet
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def eAB : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ixA ixB
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private theorem cp_block {K : Type} [Field K] (X : M4 K) (h : IsBlock X) :
    X.charpoly = (X.submatrix ixA ixA).charpoly * (X.submatrix ixB ixB).charpoly := by
  have e : Matrix.reindex eAB.symm eAB.symm X =
      Matrix.fromBlocks (X.submatrix ixA ixA) (X.submatrix ixA ixB) 0 (X.submatrix ixB ixB) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact h (ixB i) (ixA j) (by revert i j; decide)
    · rfl
  rw [← Matrix.charpoly_reindex eAB.symm, e, Matrix.charpoly_fromBlocks_zero₂₁]

private theorem det_two {K : Type} [Field K] [IsAlgClosed K] (A : Matrix (Fin 2) (Fin 2) K) :
    ∃ a ∈ A.charpoly.roots, ∃ b ∈ A.charpoly.roots, A.det = a * b := by
  have hc : A.charpoly.roots.card = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]; simp
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hc
  refine ⟨a, by simp [hab], b, by simp [hab], ?_⟩
  rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp

theorem UpperTheory.V.Ws.pureDet :
    ∀ {K : Type} [Field K] [IsAlgClosed K] (ι : K →+* ℂ) (X : M4 K), IsBlock X →
          (∀ x ∈ X.charpoly.roots, ∀ y ∈ X.charpoly.roots, ‖ι x‖ = ‖ι y‖) →
          ‖ι (X.submatrix ixA ixA).det‖ = ‖ι (X.submatrix ixB ixB).det‖ := by
  intro K _ _ ι X hX h
  have hr : X.charpoly.roots =
      (X.submatrix ixA ixA).charpoly.roots + (X.submatrix ixB ixB).charpoly.roots := by
    rw [cp_block X hX, roots_mul (mul_ne_zero (Matrix.charpoly_monic _).ne_zero (Matrix.charpoly_monic _).ne_zero)]
  obtain ⟨a, ha, b, hb, hA⟩ := det_two (X.submatrix ixA ixA)
  obtain ⟨c, hc, d, hd, hB⟩ := det_two (X.submatrix ixB ixB)
  rw [hr] at h
  rw [hA, hB, map_mul, map_mul, norm_mul, norm_mul,
    h a (Multiset.mem_add.2 (Or.inl ha)) c (Multiset.mem_add.2 (Or.inr hc)),
    h b (Multiset.mem_add.2 (Or.inl hb)) d (Multiset.mem_add.2 (Or.inr hd))]
end

