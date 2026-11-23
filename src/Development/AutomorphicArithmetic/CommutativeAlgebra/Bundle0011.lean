module

public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0010
public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineHomExistsUniqueOfGlobalSection
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private theorem comp_gamma {T : Scheme.{0}} (φ : Polynomial ℤ →+* Γ(T, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫
      (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop = CommRingCat.ofHom φ := by
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  erw [Scheme.ΓSpecIso_naturality]
  exact Iso.inv_hom_id_assoc _ _

theorem UpperTheory.affineLine_hom_existsUnique_of_globalSection :
    ∀ (T : Scheme.{0}) (a : Γ(T, ⊤)), ∃! s : T ⟶ A1, s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X) = a := by
  intro T a
  have key : ∀ s : T ⟶ A1, s = T.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫ s.appTop) := by
    intro s
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  let φ : Polynomial ℤ →+* Γ(T, ⊤) := Polynomial.eval₂RingHom (Int.castRingHom _) a
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · have h : ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫
        (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop).hom Polynomial.X = a := by
      rw [comp_gamma]
      simp [φ]
    rw [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h
  · intro s hs
    suffices e : (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫ s.appTop =
        CommRingCat.ofHom φ by
      rw [key s, e]
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · rw [CommRingCat.hom_comp, RingHom.comp_apply, hs]
      simp [φ]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CochainPullbackBijectiveOfTermwiseBijectiveInjec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.TruncCx

open GlobalTheory.ColFilt

section Abstract

variable {A B : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]

private def ConeAt (dA : ∀ n m, A n →+ A m) (dB : ∀ n m, B n →+ B m) (Φ : ∀ n, A n →+ B n)
    (n₂ : ℤ) : Prop :=
  ∀ n₀ n₁ n₃ : ℤ, n₀ + 1 = n₁ → n₁ + 1 = n₂ → n₂ + 1 = n₃ → ∀ (x : A n₂) (y : B n₁),
    dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w

variable {GA GB : ℤ → ℤ → Type*} [∀ p n, AddCommGroup (GA p n)] [∀ p n, AddCommGroup (GB p n)]
  {dA : ∀ n m, A n →+ A m} {gA : ∀ p n m, GA p n →+ GA p m} {FA : ℤ → ∀ n, AddSubgroup (A n)}
  {rA : ∀ p n m, n + p = m → (A n →+ GA p m)}
  {dB : ∀ n m, B n →+ B m} {gB : ∀ p n m, GB p n →+ GB p m} {FB : ℤ → ∀ n, AddSubgroup (B n)}
  {rB : ∀ p n m, n + p = m → (B n →+ GB p m)}

private theorem coneAt_of_graded (hA : IsFilt dA gA FA rA) (hB : IsFilt dB gB FB rB)
    (Φ : ∀ n, A n →+ B n)
    (hd : ∀ n m, n + 1 = m → ∀ x, Φ m (dA n m x) = dB n m (Φ n x))
    (hF : ∀ p n, ∀ x ∈ FA p n, Φ n x ∈ FB p n) (Ψ : ∀ p m, GA p m →+ GB p m)
    (hΨ : ∀ p n m (h : n + p = m), ∀ x ∈ FA p n, Ψ p m (rA p n m h x) = rB p n m h (Φ n x))
    (M : ℤ) (hc : ∀ p ≤ 0, ∀ k ≤ M + p, ConeAt (gA p) (gB p) (Ψ p) k)
    (n₂ : ℤ) (hn : n₂ ≤ M) : ConeAt dA dB Φ n₂ := by
  intro n₀ n₁ n₃ h01 h12 h23
  obtain ⟨N1, hN1⟩ := hA.bot n₂
  obtain ⟨N2, hN2⟩ := hB.bot n₁
  have leInd (a : ℤ) (P : ℤ → Prop) (base : P a)
      (step : ∀ n, a ≤ n → P n → P (n + 1)) : ∀ n, a ≤ n → P n := by
    intro n
    induction n using Int.inductionOn' (b := a) with
    | zero => exact fun _ => base
    | succ n hn ih => exact fun _ => step n hn (ih hn)
    | pred n hn ih => intro h; omega
  have key : ∀ p, min (min N1 N2) 0 ≤ p → p ≤ 0 → ∀ (x : A n₂) (y : B n₁), x ∈ FA p n₂ →
      y ∈ FB p n₁ → dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w := by
    intro p hNp
    refine leInd (min (min N1 N2) 0) (fun p => p ≤ 0 → ∀ (x : A n₂) (y : B n₁),
      x ∈ FA p n₂ → y ∈ FB p n₁ → dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w) ?_ ?_ p hNp
    ·
      intro _ x y hxF hyF _ _
      have hx0 : x = 0 := hN1 x (hA.mono _ N1 n₂ (by omega) hxF)
      have hy0 : y = 0 := hN2 y (hB.mono _ N2 n₁ (by omega) hyF)
      exact ⟨0, 0, by simp [hx0], by simp [hy0]⟩
    · intro q hNq ih
      intro hq x y hxF hyF hx hxy
      have ih' := ih (by omega)
      have hpq : q + 1 - 1 = q := by ring
      obtain ⟨v₀, w₀, hv₀, hw₀⟩ := hc (q + 1) hq (n₂ + (q + 1)) (by omega)
        (n₀ + (q + 1)) (n₁ + (q + 1)) (n₃ + (q + 1)) (by omega) (by omega) (by omega)
        (rA (q + 1) n₂ _ rfl x) (rB (q + 1) n₁ _ rfl y)
        (by rw [← hA.rd (q + 1) n₂ n₃ _ _ rfl rfl h23 x hxF, hx, map_zero])
        (by rw [hΨ (q + 1) n₂ _ rfl x hxF, hxy, hB.rd (q + 1) n₁ n₂ _ _ rfl rfl h12 y hyF])
      obtain ⟨v, hvF, hv⟩ := hA.surj (q + 1) n₁ _ rfl v₀
      obtain ⟨w, hwF, hw⟩ := hB.surj (q + 1) n₀ _ rfl w₀
      have hx'F : x - dA n₁ n₂ v ∈ FA q n₂ := by
        have h := (hA.ker (q + 1) n₂ _ rfl (x - dA n₁ n₂ v)
          (sub_mem hxF (hA.dF (q + 1) n₁ n₂ h12 v hvF))).1
          (by rw [map_sub, hA.rd (q + 1) n₁ n₂ _ _ rfl rfl h12 v hvF, hv, hv₀, sub_self])
        rwa [hpq] at h
      have hy'F : y - Φ n₁ v - dB n₀ n₁ w ∈ FB q n₁ := by
        have h := (hB.ker (q + 1) n₁ _ rfl (y - Φ n₁ v - dB n₀ n₁ w)
          (sub_mem (sub_mem hyF (hF (q + 1) n₁ v hvF)) (hB.dF (q + 1) n₀ n₁ h01 w hwF))).1
          (by
            rw [map_sub, map_sub, ← hΨ (q + 1) n₁ _ rfl v hvF,
              hB.rd (q + 1) n₀ n₁ _ _ rfl rfl h01 w hwF, hv, hw, hw₀]
            abel)
        rwa [hpq] at h
      have hx'c : dA n₂ n₃ (x - dA n₁ n₂ v) = 0 := by
        rw [map_sub, hx, hA.dd, sub_self]
      have hx'r : Φ n₂ (x - dA n₁ n₂ v) = dB n₁ n₂ (y - Φ n₁ v - dB n₀ n₁ w) := by
        rw [map_sub, map_sub, map_sub, hd n₁ n₂ h12 v, hxy, hB.dd, sub_zero]
      obtain ⟨v', w', hv', hw'⟩ := ih' _ _ hx'F hy'F hx'c hx'r
      refine ⟨v + v', w + w', ?_, ?_⟩
      · rw [map_add (f := _), ← hv']
        abel
      · rw [map_add (f := _), map_add (f := _)]
        rw [sub_sub, sub_eq_iff_eq_add] at hw'
        rw [hw']
        abel
  intro x y hx hxy
  exact key 0 (by omega) le_rfl x y (hA.top n₂ x) (hB.top n₁ y) hx hxy

end Abstract

section Classes

variable {R : Type} [CommRing R]

private def pre {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) : Cochain L I n →+ Cochain K I n :=
  AddMonoidHom.mk' (fun α => (Cochain.ofHom g).comp α (zero_add n))
    (fun _ _ => Cochain.comp_add _ _ _ _)

private theorem pre_v {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) (α : Cochain L I n) (t q : ℤ)
    (hq : t + n = q) : (pre g I n α).v t q hq = g.f t ≫ α.v t q hq := by
  simp [pre, Cochain.comp_zero_cochain_v]

private theorem pre_δ {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n m : ℤ) (h : n + 1 = m)
    (α : Cochain L I n) : pre g I m (δ n m α) = δ n m (pre g I n α) := by
  simp only [pre, AddMonoidHom.mk'_apply]
  rw [δ_ofHom_comp]

private theorem cpull_mk_eq_mk_of_pre {K L I : Cx R} (g : K ⟶ L) (n : ℤ) (x : Cocycle L I n)
    (z : Cocycle K I n) (hz : (z : Cochain K I n) = pre g I n x) :
    cpull g I n (CohomologyClass.mk x) = CohomologyClass.mk z := by
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  exact Subtype.ext (by rw [hz]; rfl)

private theorem coneAt_of_conn {K L I : Cx R} (g : K ⟶ L) (M : ℤ)
    (hb : ∀ n, n < M → Function.Bijective (cpull g I n)) (hi : Function.Injective (cpull g I M))
    (k : ℤ) (hk : k ≤ M) : ConeAt (dC L I) (dC K I) (pre g I) k := by
  intro n₀ n₁ n₃ h01 h12 h23 x y hx hxy
  simp only [dC, AddMonoidHom.mk'_apply] at hx hxy ⊢
  have hk1 : n₁ < M := by omega
  have injk : Function.Injective (cpull g I k) := by
    rcases lt_or_eq_of_le hk with h | h
    · exact (hb k h).1
    · subst h
      exact hi
  have hpx : δ k n₃ (pre g I k x) = 0 := by rw [← pre_δ g I k n₃ h23, hx, map_zero]
  have e1 : cpull g I k (CohomologyClass.mk (Cocycle.mk x n₃ h23 hx)) = 0 := by
    rw [cpull_mk_eq_mk_of_pre g k _ (Cocycle.mk (pre g I k x) n₃ h23 hpx) rfl, ← CohomologyClass.mk_zero,
      mk_eq_mk_iff _ _ n₁ h12]
    exact ⟨y, by simp [hxy]⟩
  have e2 := injk (e1.trans (map_zero _).symm)
  rw [← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ n₁ h12] at e2
  obtain ⟨v', hv'⟩ := e2
  simp only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hv'
  have hyc : δ n₁ k (y - pre g I n₁ v') = 0 := by
    rw [δ_sub, ← pre_δ g I n₁ k h12, hv', hxy, sub_self]
  obtain ⟨c, hc⟩ := (hb n₁ hk1).2 (CohomologyClass.mk (Cocycle.mk _ k h12 hyc))
  obtain ⟨u, rfl⟩ := CohomologyClass.mk_surjective c
  have hpu : δ n₁ k (pre g I n₁ u) = 0 := by
    rw [← pre_δ g I n₁ k h12, Cocycle.δ_eq_zero, map_zero]
  rw [cpull_mk_eq_mk_of_pre g n₁ u (Cocycle.mk (pre g I n₁ u) k h12 hpu) rfl, mk_eq_mk_iff _ _ n₀ h01] at hc
  obtain ⟨w, hw⟩ := hc
  simp only [Cocycle.mk_coe] at hw
  refine ⟨v' + u, -w, ?_, ?_⟩
  · rw [δ_add, hv', Cocycle.δ_eq_zero, add_zero]
  · rw [map_add (f := _), δ_neg, hw]
    abel

private theorem conn_of_coneAt {K L I : Cx R} (g : K ⟶ L) (M : ℤ)
    (h : ∀ k ≤ M, ConeAt (dC L I) (dC K I) (pre g I) k) :
    (∀ n, n < M → Function.Bijective (cpull g I n)) ∧ Function.Injective (cpull g I M) := by
  have inj : ∀ n, n ≤ M → Function.Injective (cpull g I n) := by
    intro n hn
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective c
    have hpx : δ n (n + 1) (pre g I n x) = 0 := by
      rw [← pre_δ g I n (n + 1) rfl, Cocycle.δ_eq_zero, map_zero]
    rw [cpull_mk_eq_mk_of_pre g n x (Cocycle.mk _ (n + 1) rfl hpx) rfl, ← CohomologyClass.mk_zero,
      mk_eq_mk_iff _ _ (n - 1) (by ring)] at hc
    obtain ⟨y, hy⟩ := hc
    simp only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hy
    obtain ⟨v, w, hv, -⟩ := h n hn (n - 1 - 1) (n - 1) (n + 1) (by ring) (by ring) rfl
      (x : Cochain L I n) y (Cocycle.δ_eq_zero x _) (by simp only [dC, AddMonoidHom.mk'_apply, hy])
    rw [← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ (n - 1) (by ring)]
    simp only [dC, AddMonoidHom.mk'_apply] at hv
    exact ⟨v, by rw [← hv]; simp⟩
  refine ⟨fun n hn => ⟨inj n hn.le, ?_⟩, inj M le_rfl⟩
  intro c
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨v, w, hv, hw⟩ := h (n + 1) (by omega) (n - 1) n (n + 1 + 1) (by ring) rfl rfl 0
    (z : Cochain K I n) (map_zero _) (by simp [dC, Cocycle.δ_eq_zero])
  simp only [dC, AddMonoidHom.mk'_apply] at hv hw
  have hvδ : δ n (n + 1) v = 0 := hv.symm
  have hpv : δ n (n + 1) (pre g I n v) = 0 := by
    rw [← pre_δ g I n (n + 1) rfl, hvδ, map_zero]
  refine ⟨CohomologyClass.mk (Cocycle.mk v (n + 1) rfl hvδ), ?_⟩
  rw [cpull_mk_eq_mk_of_pre g n _ (Cocycle.mk (pre g I n v) (n + 1) rfl hpv) rfl,
    mk_eq_mk_iff _ _ (n - 1) (by ring)]
  refine ⟨-w, ?_⟩
  simp only [Cocycle.mk_coe, δ_neg, hw]
  abel

end Classes

end UpperTheory.TruncCx

private theorem ιTerm_comp_f_naturality {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (c k t : ℤ)
    (h : c + k = t) :
    GlobalTheory.ColFilt.ιTerm K c k t h ≫ g.f t =
      ((CochainComplex.singleFunctor (Shv R) 0).map (g.f c)).f k ≫ GlobalTheory.ColFilt.ιTerm L c k t h := by
  by_cases hk : k = 0
  · subst hk
    have hct : t = c := by omega
    subst hct
    rw [GlobalTheory.ColFilt.ιTerm_zero, GlobalTheory.ColFilt.ιTerm_zero]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self]
  · rw [GlobalTheory.ColFilt.ιTerm_ne K c k t h hk, GlobalTheory.ColFilt.ιTerm_ne L c k t h hk]
    simp

open GlobalTheory.ColFilt UpperTheory.TruncCx in
theorem UpperTheory.cochainPullback_bijective_of_termwise_bijective_injective :
    ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) → ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (m : ℤ), (∀ p : ℤ, (∀ n, n < m + p → Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) ∧ Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I (m + p))) → (∀ n, n < m → Function.Bijective (cpull g I n)) ∧ Function.Injective (cpull g I m) := by
  intro R _ I _ _ K L _ _ g m hyp
  apply UpperTheory.TruncCx.conn_of_coneAt g m
  intro k hk
  refine UpperTheory.TruncCx.coneAt_of_graded ((isColumns_terms L).isFilt I) ((isColumns_terms K).isFilt I)
    (UpperTheory.TruncCx.pre g I) (fun n m' h x => UpperTheory.TruncCx.pre_δ g I n m' h x) ?_
    (fun p => UpperTheory.TruncCx.pre ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I) ?_ m
    (fun p _ k' hk' => UpperTheory.TruncCx.coneAt_of_conn _ (m + p) (hyp p).1 (hyp p).2 k' hk') k hk
  · intro p n x hx c k' t h q hq hpc
    have hx' : ∀ (c k t : ℤ) (h : c + k = t) (q : ℤ) (hq : t + n = q), p < c →
        ιTerm L c k t h ≫ x.v t q hq = 0 := hx
    rw [UpperTheory.TruncCx.pre_v, ← Category.assoc, ιTerm_comp_f_naturality, Category.assoc,
      hx' c k' t h q hq hpc, comp_zero]
  · intro p n m' h x _
    refine Cochain.ext _ _ (fun k' q hq => ?_)
    rw [UpperTheory.TruncCx.pre_v, restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega),
      restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega), UpperTheory.TruncCx.pre_v,
      ← Category.assoc, ← Category.assoc, ιTerm_comp_f_naturality]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectivityOfCechDisjointCover
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_square {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {E₁ E₂ E₃ E₄ : Spc} {u : E₁ ⟶ E₂}
    {v : E₃ ⟶ E₄} {a : E₁ ⟶ E₃} {b : E₂ ⟶ E₄} (w : u ≫ b = a ≫ v) (ha : Eqv R a F) (hb : Eqv R b F)
    (hu : Conn R F c u) : Conn R F c v := by
  have key : ∀ (n : ℤ) (x : H R E₄ F n), pull R a F n (pull R v F n x) = pull R u F n (pull R b F n x) := by
    intro n x
    rw [← pull_comp, ← pull_comp, w]
  have inj : ∀ n : ℤ, Function.Injective (pull R u F n) → Function.Injective (pull R v F n) := by
    intro n hi x y h
    exact (hb n).1 (hi ((key n x).symm.trans ((congrArg _ h).trans (key n y))))
  have sur : ∀ n : ℤ, Function.Surjective (pull R u F n) → Function.Surjective (pull R v F n) := by
    intro n hs y
    obtain ⟨z, hz⟩ := hs (pull R a F n y)
    obtain ⟨x, rfl⟩ := (hb n).2 z
    exact ⟨x, (ha n).1 ((key n x).trans hz)⟩
  intro n
  exact ⟨fun hn => ⟨inj n ((hu n).1 hn).1, sur n ((hu n).1 hn).2⟩, fun hn => inj n ((hu n).2 hn)⟩

private theorem eqv_of_iso {R : Type} [CommRing R] {F : Shv R} {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

private theorem conn_level {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {P Q : PSh} (ψ : P ⟶ Q) {Z Z' : Scheme.{0}}
    (k : Z' ⟶ Z) (e : yoneda.obj Z ≅ Q) (e' : yoneda.obj Z' ≅ P) (h : e'.hom ≫ ψ = yoneda.map k ≫ e.hom)
    (hk : Conn R F c (sch.map k)) : Conn R F c (disc.map ψ) := by
  refine conn_square (u := sch.map k) (a := (disc.mapIso e').hom) (b := (disc.mapIso e).hom) ?_
    (eqv_of_iso _) (eqv_of_iso _) hk
  change disc.map (yoneda.map k) ≫ disc.map e.hom = disc.map e'.hom ≫ disc.map ψ
  rw [← Functor.map_comp, ← Functor.map_comp, h]

private theorem cech_zero {V Y : Scheme.{0}} (f : V ⟶ Y) :
    ∃ e : yoneda.obj V ≅ (cech f).obj (op (SimplexCategory.mk 0)),
      e.hom ≫ (cechAug f).app (op (SimplexCategory.mk 0)) = yoneda.map f := by
  let π₀ : Fin 1 → (yoneda.obj V ⟶ yoneda.obj Y) := fun _ => yoneda.map f
  let h : yoneda.obj V ⟶ widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ :=
    WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  let k : widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ ⟶ yoneda.obj V :=
    WidePullback.π π₀ 0
  have hk : h ≫ k = 𝟙 _ := WidePullback.lift_π _ _ _ _ _
  have hb : h ≫ WidePullback.base π₀ = yoneda.map f := WidePullback.lift_base _ _ _ _
  have kh : k ≫ h = 𝟙 _ := by
    apply WidePullback.hom_ext
    · intro j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [Category.assoc, Category.id_comp]
      change k ≫ h ≫ k = k
      rw [hk, Category.comp_id]
    · rw [Category.assoc, hb, Category.id_comp]
      exact WidePullback.π_arrow π₀ 0
  exact ⟨⟨h, k, hk, kh⟩, hb⟩

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_of_cover {V Y : Scheme.{0}} (f : V ⟶ Y)
    (hcov : ∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) :
    Smooth f := by
  obtain ⟨ι, O, j, hj, -, hc, hf⟩ := hcov
  let 𝒰 : V.OpenCover := Scheme.Cover.mkOfCovers ι O j (fun y => by
    obtain ⟨a, x, hx⟩ := hc y
    exact ⟨a, x, hx⟩)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 fun a => ?_
  have := hf a
  change Smooth (j a ≫ f)
  infer_instance

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ConstantSheafCyclicGeneratorOfOrder
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

private theorem UpperTheory.continuousSection_nsmul (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T]
    [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (U : Scheme.{0})
    (a : C(U, T)) (c : ℕ) : cSec R T (c • a) = c • cSec R T a := by
  exact map_nsmul (AddMonoidHom.mk' (cSec R T (U := U)) (UpperTheory.continuousSections_bijective_additive_natural R T U).2.1) c a

private theorem UpperTheory.restriction_comp {R : Type} [CommRing R] (M : PMod R) {W' W V : Scheme.{0}}
    (l : W' ⟶ W) (h : W ⟶ V) (z : sec M V) : rs M (l ≫ h) z = rs M l (rs M h z) := by
  simp only [rs, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem UpperTheory.constantSheaf_cyclic_generator_of_order :
    ∀ (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [DiscreteTopology T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (q : ℕ) (t : T), q • t = 0 → (∀ c : ℕ, c • t = 0 → q ∣ c) → (∀ x : T, ∃ c : ℕ, x = c • t) → ∀ U : Scheme.{0}, Gen Scheme.etaleTopology q (cSh R T).obj (cSec R T (ContinuousMap.const U t)) := by
  intro R _ T _ _ _ _ _ _ q t hq hmin hgen U
  have hsm : ∀ (W : Scheme.{0}) (a : C(W, T)) (c : ℕ), cSec R T (c • a) = c • cSec R T a :=
    fun W a c => UpperTheory.continuousSection_nsmul R T W a c
  have h0 : ∀ W : Scheme.{0}, cSec R T (0 : C(W, T)) = 0 := fun W =>
    map_zero (AddMonoidHom.mk' (cSec R T (U := W)) (UpperTheory.continuousSections_bijective_additive_natural R T W).2.1)
  have hrs : ∀ (V : Scheme.{0}) (k : V ⟶ U),
      rs (cSh R T).obj k (cSec R T (ContinuousMap.const U t)) =
        cSec R T (ContinuousMap.const V t) := by
    intro V k
    rw [(UpperTheory.continuousSections_bijective_additive_natural R T U).2.2.1]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsm, show q • ContinuousMap.const U t = 0 by ext; simp [hq], h0]
  · intro V k c hV hc
    obtain ⟨v⟩ := hV
    rw [hrs, ← hsm, ← h0 V] at hc
    have he := (UpperTheory.continuousSections_bijective_additive_natural R T V).1.1 hc
    have hv : c • t = 0 := by simpa using congrArg (fun f : C(V, T) => f v) he
    exact hmin c hv
  · intro V k y
    obtain ⟨b, rfl⟩ := (UpperTheory.continuousSections_bijective_additive_natural R T V).1.2 y
    refine (UpperTheory.etaleLocallyHolds_of_pointwise_cover_or_affine_local V _ ?_).1 ?_
    · rintro W W' g' k' ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [UpperTheory.restriction_comp _ k' g', hc, Category.assoc, UpperTheory.restriction_comp _ k' (g' ≫ k)]
      exact map_nsmul ((cSh R T).obj.map k'.op).hom c _
    · intro x
      obtain ⟨c, hc⟩ := hgen (b x)
      let O : V.Opens := ⟨b ⁻¹' {b x}, (isOpen_discrete _).preimage b.continuous⟩
      refine ⟨O, O.ι, inferInstance, ?_, c, ?_⟩
      · rw [Scheme.Opens.range_ι]
        show b x ∈ ({b x} : Set T)
        exact Set.mem_singleton _
      · rw [(UpperTheory.continuousSections_bijective_additive_natural R T V).2.2.1, hrs, ← hsm]
        congr 1
        ext w
        have hw : O.ι w ∈ (O : Set V) := Scheme.Opens.range_ι O ▸ Set.mem_range_self w
        have hw' : b (O.ι w) = b x := hw
        simp [hw', hc]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyIsUnitOrIsUnitOfSpanPairEqTop
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private theorem unit_on_basicOpen (T : Scheme.{0}) (a : Γ(T, ⊤)) :
    IsUnit ((T.basicOpen a).ι.appTop.hom a) := by
  have hb := Scheme.Opens.ι_preimage_self (T.basicOpen a)
  rw [Scheme.preimage_basicOpen] at hb
  apply RingedSpace.isUnit_of_isUnit_germ _ ⊤
  intro x hx
  have hx' : x ∈ (T.basicOpen a).toScheme.basicOpen
      ((ConcreteCategory.hom ((T.basicOpen a).ι.app ⊤)) a) := by
    rw [hb]
    trivial
  exact (Scheme.mem_basicOpen _ _ x hx).mp hx'

private theorem mem_basicOpen_or (T : Scheme.{0}) (a b : Γ(T, ⊤)) (h : Ideal.span {a, b} = ⊤) (u : T) :
    u ∈ T.basicOpen a ∨ u ∈ T.basicOpen b := by
  have h1 : (1 : Γ(T, ⊤)) ∈ Ideal.span {a, b} := h ▸ Submodule.mem_top
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp h1
  have hu : IsUnit (ConcreteCategory.hom (T.presheaf.germ ⊤ u trivial) (x * a) +
      ConcreteCategory.hom (T.presheaf.germ ⊤ u trivial) (y * b)) := by
    rw [← map_add (f := _), hxy, map_one]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with hx | hy
  · left
    rw [Scheme.mem_basicOpen_top]
    rw [map_mul] at hx
    exact isUnit_of_mul_isUnit_right hx
  · right
    rw [Scheme.mem_basicOpen_top]
    rw [map_mul] at hy
    exact isUnit_of_mul_isUnit_right hy

theorem UpperTheory.locally_isUnit_or_isUnit_of_span_pair_eq_top :
    ∀ (T : Scheme.{0}) (a b : Γ(T, ⊤)), Ideal.span {a, b} = ⊤ → Loc T fun V g => IsUnit (g.appTop.hom a) ∨ IsUnit (g.appTop.hom b) := by
  intro T a b h
  let U : Bool → T.Opens := fun i => bif i then T.basicOpen a else T.basicOpen b
  have hU : TopologicalSpace.IsOpenCover U := by
    apply eq_top_iff.mpr
    intro u _
    rcases mem_basicOpen_or T a b h u with hu | hu
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, hu⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hu⟩
  let C := T.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.ofArrows C.X C.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology C), ?_⟩
  intro V g hg
  obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  cases i
  · right
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (unit_on_basicOpen T b).map c.appTop.hom
  · left
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (unit_on_basicOpen T a).map c.appTop.hom
end

