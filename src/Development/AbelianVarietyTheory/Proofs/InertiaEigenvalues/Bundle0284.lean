module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism

namespace GlobalTheory.Prism.LocalValue

theorem exists_basis {A B M N ι : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Fintype ι] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (b : Module.Basis ι A M) : ∃ c : Module.Basis ι B N, ∀ i, c i = u (b i) := by
  classical
  let v : M →ₛₗ[f] (ι → B) :=
    { toFun := fun x i => f (b.equivFun x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  let Q : (ι → B) →ₗ[B] N := Fintype.linearCombination B fun i => u (b i)
  have hQ : Q.comp S = LinearMap.id := h.hom_ext fun x => by
    rw [LinearMap.comp_apply, hS, LinearMap.id_apply, Fintype.linearCombination_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← b.sum_equivFun x, map_sum]
    exact Finset.sum_congr rfl fun i _ => (u.map_smulₛₗ _ _).symm
  have hQ1 : ∀ i, Q (Pi.single i 1) = u (b i) := fun i => by
    simp [Q]
  have hS' : S.comp Q = LinearMap.id := by
    refine (Pi.basisFun B ι).ext fun i => ?_
    rw [LinearMap.comp_apply, Pi.basisFun_apply, hQ1, hS, LinearMap.id_apply]
    ext k
    change f (b.equivFun (b i) k) = _
    rw [b.equivFun_self, Pi.single_apply]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik, Ne.symm hik]
  refine ⟨(Pi.basisFun B ι).map (LinearEquiv.ofLinear Q S hQ hS'), fun i => ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  exact hQ1 i

theorem exists_pow_smul_eq_sum {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
    {d : A} {f : A →+* Localization.Away d} {Φ : M →ₛₗ[f] LocalizedModule (Submonoid.powers d) M}
    (h : SemiBC Φ) (b : Module.Basis ι A M) (m : ι → M) (k : ι → ℕ)
    (hm : ∀ i, IsFrac d (Φ (b i)) (m i) (k i)) (x : M) :
    ∃ (r : ℕ) (s : ι → A), d ^ r • x = ∑ i, s i • m i := by
  obtain ⟨c, hc⟩ := exists_basis h b
  have h1 : (LocalizedModule.mk x 1 : LocalizedModule (Submonoid.powers d) M) ∈
      Submodule.span (Localization.Away d)
        (Set.range fun i => (LocalizedModule.mk (m i) 1 : LocalizedModule (Submonoid.powers d) M)) := by
    refine (?_ : (⊤ : Submodule (Localization.Away d) _) ≤ _) Submodule.mem_top
    rw [← c.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h2 : c i = (Localization.mk 1 ⟨d ^ k i, (Submonoid.mem_powers_iff _ _).2 ⟨k i, rfl⟩⟩ :
        Localization.Away d) • (LocalizedModule.mk (m i) 1 : LocalizedModule (Submonoid.powers d) M) := by
      rw [hc, hm i, LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨⟨_, t, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span (Submonoid.powers d)
    (Localization.Away d) _ _ h1
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ht
  have h3 : LocalizedModule.mkLinearMap (Submonoid.powers d) M (∑ i, s i • m i) =
      LocalizedModule.mkLinearMap (Submonoid.powers d) M (d ^ t • x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul]
    simp only [map_smul]
    exact hs
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq] at h3
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := h3
  simp only [one_smul, Submonoid.smul_def] at ha
  refine ⟨a + t, fun i => d ^ a * s i, ?_⟩
  rw [pow_add, mul_smul, ← ha, Finset.smul_sum]
  simp only [mul_smul]

theorem exists_eq_smul {A B M N ι : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Fintype ι] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (b : Module.Basis ι A M) {π : A} (hπ : RingHom.ker f = Ideal.span {π}) (x : M) (hx : u x = 0) :
    ∃ y, x = π • y := by
  obtain ⟨c, hc⟩ := exists_basis h b
  have h1 : ∑ i, f (b.equivFun x i) • c i = 0 := by
    rw [← hx]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← b.sum_equivFun x, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hc, u.map_smulₛₗ]
  have h2 := Fintype.linearIndependent_iff.1 c.linearIndependent _ h1
  have h3 : ∀ i, ∃ a, a * π = b.equivFun x i := fun i =>
    Ideal.mem_span_singleton'.1 (hπ ▸ (RingHom.mem_ker).2 (h2 i))
  choose a ha using h3
  refine ⟨∑ i, a i • b i, ?_⟩
  conv_lhs => rw [← b.sum_equivFun x]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← ha, smul_smul, mul_comm]

theorem ennreal_volume_ratio_step_cancel {A B M N : Type} [CommRing A] [CommRing B] [IsDomain B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Module.Free B N] {f : A →+* B} (u : M →ₛₗ[f] N) {e : A}
    (he : f e ≠ 0) {m n : M} {k i r : ℕ} (h : (e * e) ^ r • (e ^ i • m - e ^ k • n) = 0) {y : N}
    (hy : f e ^ i • y = u n) : f e ^ k • y = u m := by
  have h2 := congrArg u h
  rw [u.map_smulₛₗ, map_sub, u.map_smulₛₗ, u.map_smulₛₗ, map_zero, map_pow, map_pow, map_pow, map_mul,
    ← hy, smul_comm (f e ^ k), ← smul_sub, smul_eq_zero, smul_eq_zero] at h2
  rcases h2 with h2 | h2 | h2
  · exact absurd h2 (pow_ne_zero _ (mul_ne_zero he he))
  · exact absurd h2 (pow_ne_zero _ he)
  · exact (sub_eq_zero.1 h2).symm

theorem general {l : ℕ} {R : Type} [CommRing R] {PS PA : Obj l R} [IsLocalRing PS.A] (io : Hom PS PA)
    {B N : Type} [CommRing B] [IsDomain B] [AddCommGroup N] [Module B N] {f : PA.A →+* B}
    (E : FCrys l R) {j : E.M PA →ₛₗ[f] N} (hj : SemiBC j) (F : N → N)
    (hF : ∀ (d : ↥PA.I), (d : PA.A) ≠ 0 → ∀ (x m : E.M PA) (k : ℕ), IsFrac (d : PA.A) (E.Φ PA d x) m k →
      f d ^ k • F (j x) = j m)
    {Q : PS.A} (hQ : Q ∈ PS.I) (ψ : PS.A →+* B) (hψ : ∀ x, ψ x = f (io.f x)) (hQ0 : ψ Q ≠ 0) :
    ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) B N),
      (∀ i, c i = j (E.tr io (b i))) ∧
      (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • F (j (E.tr io x)) = j (E.tr io m)) ∧
      (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr io x) = ∑ i, ψ (s i) • F (c i)) := by
  have := E.fin PS
  have := E.proj PS
  have : Module.Free PS.A (E.M PS) := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis PS.A (E.M PS)
  obtain ⟨c', hc'⟩ := exists_basis (E.tr_bc io) b
  obtain ⟨c, hc⟩ := exists_basis hj c'
  have hcb : ∀ i, c i = j (E.tr io (b i)) := fun i => by rw [hc, hc']
  have : Module.Free B N := Module.Free.of_basis c
  have hsm : ∀ (s : PS.A) (x : E.M PS), j (E.tr io (s • x)) = ψ s • j (E.tr io x) := fun s x => by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hψ]
  have key : ∀ (x m : E.M PS) (k : ℕ), IsFrac Q (E.Φ PS ⟨Q, hQ⟩ x) m k →
      ψ Q ^ k • F (j (E.tr io x)) = j (E.tr io m) := by
    intro x m k h
    have h0 : io.f Q ≠ 0 := fun h0 => hQ0 (by rw [hψ, h0, map_zero])
    obtain ⟨n, i, hn⟩ := exists_isFrac (io.f Q) (E.Φ PA ⟨io.f Q, io.f_I Q hQ⟩ (E.tr io x))
    obtain ⟨r, hr⟩ := E.Φ_nat io ⟨Q, hQ⟩ ⟨io.f Q, io.f_I Q hQ⟩ x m k n i h hn
    have h1 := hF ⟨io.f Q, io.f_I Q hQ⟩ h0 _ n i hn
    rw [hψ] at hQ0 ⊢
    exact ennreal_volume_ratio_step_cancel j hQ0 hr h1
  refine ⟨_, b, c, hcb, fun x => ?_, fun x => ?_⟩
  · obtain ⟨m, k, h⟩ := exists_isFrac Q (E.Φ PS ⟨Q, hQ⟩ x)
    exact ⟨k, m, key x m k h⟩
  · choose m k hm using fun i => exists_isFrac Q (E.Φ PS ⟨Q, hQ⟩ (b i))
    obtain ⟨r, s, hs⟩ := exists_pow_smul_eq_sum (E.Φ_bc PS ⟨Q, hQ⟩) b m k hm x
    refine ⟨r, fun i => s i * Q ^ k i, ?_⟩
    have hs' : Q ^ r • x = ∑ i, s i • m i := hs
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_pow, ← hsm, hs', map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsm, ← key _ _ _ (hm i), hcb, smul_smul, map_mul, map_pow]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (PS PW : Obj l ↥(OL K)) (ev : Hom PS PW) (ioH : Hom PS (ainfObj K)) (gH : ↥(GK K) → Hom PS PS) (π Q : PS.A) (ψ : PS.A →+* WCb l), (∀ x, ψ x = inclW l (ainfId K (ioH.f x))) → (∀ g, ioH.comp (gH g) = (ainfHom K g).comp ioH) → (∀ g, ev.comp (gH g) = ev) → RingHom.ker ev.f = Ideal.span {π} → Q ∈ PS.I → IsLocalRing PS.A → ψ Q ≠ 0 → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (E : FCrys l ↥(OL K)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) (WCb l) (WCb l ⊗[ℤ_[l]] T)), (∀ i, c i = j (E.tr ioH (b i))) ∧ (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (E.tr ioH x)) = j (E.tr ioH m)) ∧ (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr ioH x) = ∑ i, ψ (s i) • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c i)) ∧ (∀ (g : ↥(GK K)) x, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j (E.tr ioH x)) = j (E.tr ioH (E.tr (gH g) x))) ∧ (∀ g x, ∃ y, E.tr (gH g) x - x = π • y) := by
  intro l _ K PS PW ev ioH gH π Q ψ hψ hg hev hker hQ hloc hQ0 T _ _ ρ E j H
  obtain ⟨q, b, c, h1, h2, h3⟩ := general ioH E H.bc
    (fun y => TensorProduct.map (frobW l).toLinearMap LinearMap.id y) H.j_φ hQ ψ hψ hQ0
  refine ⟨q, b, c, h1, h2, h3, fun g x => ?_, fun g x => ?_⟩
  · have h4 : E.tr ioH (E.tr (gH g) x) = E.tr (ainfHom K g) (E.tr ioH x) :=
      ((E.tr_comp ioH (gH g) x).symm.trans (congrArg (fun f => E.tr f x) (hg g))).trans
        (E.tr_comp (ainfHom K g) ioH x)
    exact (H.j_act g (E.tr ioH x)).symm.trans (congrArg j h4.symm)
  · refine exists_eq_smul (E.tr_bc ev) b hker _ ?_
    rw [map_sub, ← E.tr_comp, hev, sub_self]

end GlobalTheory.Prism.LocalValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReducibleOfStableRationalRowSubspace
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem vecMul_repr_rows {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n E (n → E)) (v : n → E) :
    Matrix.vecMul v (Matrix.of fun k j => b.repr (Pi.single k 1) j) = b.repr v := by
  ext j
  conv_rhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (v k) : n → E) = v k • Pi.single k 1 by
    ext i; by_cases h : i = k <;> simp [h]]
  simp

theorem vecMul_rows_repr {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n E (n → E)) (v : n → E) :
    Matrix.vecMul (b.repr v) (Matrix.of fun i j => b i j) = v := by
  ext j
  conv_rhs => rw [← b.sum_repr v]
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem splits_of_stable_rat_subspace : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → ∀ W : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)), (∀ c ∈ W, ∀ i, fr l r (c i) = c i) → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c ∈ W, e • c ∈ W) → (∀ g, ∀ c ∈ W, Matrix.vecMul c (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) ∈ W) → W ≠ ⊥ → (∃ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) ∧ c ∉ W) → Splits r ρ := by
  classical
  intro l _ n _ _ K r ρ hρ W hWE hWsm hWst hW0 hWtop
  let E : Subfield ↥(MaximalUnramifiedExtension l) := RingHom.eqLocusField (fr l r) (RingHom.id _)
  let ι : E →+* ↥(MaximalUnramifiedExtension l) := E.subtype
  have hE : ∀ x : E, fr l r (x : ↥(MaximalUnramifiedExtension l)) = x := fun x => x.2
  let cv : (n → E) → (n → ↥(MaximalUnramifiedExtension l)) := fun c i => (c i : ↥(MaximalUnramifiedExtension l))
  let W' : Submodule E (n → E) :=
    { carrier := {c | cv c ∈ W}
      add_mem' := fun {c d} hc hd => by
        show cv (c + d) ∈ W
        rw [show cv (c + d) = cv c + cv d from funext fun i => by simp [cv]]
        exact W.add_mem hc hd
      zero_mem' := by
        show cv 0 ∈ W
        rw [show cv 0 = 0 from funext fun i => by simp [cv]]
        exact W.zero_mem
      smul_mem' := fun e c hc => by
        show cv (e • c) ∈ W
        rw [show cv (e • c) = (e : ↥(MaximalUnramifiedExtension l)) • cv c from funext fun i => by simp [cv, smul_eq_mul]]
        exact hWsm (e : ↥(MaximalUnramifiedExtension l)) (hE e) _ hc }
  have memW' : ∀ c, c ∈ W' ↔ cv c ∈ W := fun c => Iff.rfl
  have lift : ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∃ c' : n → E, cv c' = c :=
    fun c hc => ⟨fun i => ⟨c i, hc i⟩, rfl⟩
  have hW'0 : W' ≠ ⊥ := by
    obtain ⟨c, hcW, hc0⟩ : ∃ c ∈ W, c ≠ 0 := by
      by_contra h
      push_neg at h
      exact hW0 ((AddSubgroup.eq_bot_iff_forall W).2 h)
    obtain ⟨c', rfl⟩ := lift c (hWE c hcW)
    intro h
    have : c' ∈ W' := hcW
    rw [h, Submodule.mem_bot] at this
    exact hc0 (by subst this; rfl)
  have hW'top : W' ≠ ⊤ := by
    obtain ⟨c, hcE, hcW⟩ := hWtop
    obtain ⟨c', rfl⟩ := lift c hcE
    intro h
    exact hcW ((memW' c').1 (h ▸ Submodule.mem_top))
  obtain ⟨S, hSW, hSspan, hSli⟩ := exists_linearIndependent E (W' : Set (n → E))
  have hSli' : LinearIndepOn E id S := hSli
  let B := Module.Basis.extend hSli'
  let e := B.indexEquiv (Pi.basisFun E n)
  let b : Module.Basis n E (n → E) := B.reindex e
  have hb : ∀ i, b i = ((e.symm i : _) : n → E) := fun i => by
    rw [Module.Basis.reindex_apply]; exact Module.Basis.extend_apply_self hSli' _
  have hbS : ∀ x ∈ S, ∃ i, b i = x := fun x hx =>
    ⟨e ⟨x, Module.Basis.subset_extend hSli' hx⟩, by simp [hb]⟩
  let s : Finset n := Finset.univ.filter fun i => b i ∉ S
  have hs : ∀ i, i ∉ s ↔ b i ∈ S := fun i => by simp [s]
  have hWspan : W' ≤ Submodule.span E (b '' ((s : Set n)ᶜ)) := by
    conv_lhs => rw [← Submodule.span_eq W', ← hSspan]
    apply Submodule.span_mono
    intro x hx
    obtain ⟨i, rfl⟩ := hbS x hx
    exact ⟨i, by simpa [hs] using hx, rfl⟩
  have hsne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hW'top
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hSW ((hs i).1 (by simp [h]))
  have hsuniv : s ≠ Finset.univ := by
    intro h
    apply hW'0
    have hS0 : S = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨i, rfl⟩ := hbS x hx
      exact (hs i).2 hx (by simp [h])
    rw [← Submodule.span_eq W', ← hSspan, hS0, Submodule.span_empty]
  let M : Matrix n n E := Matrix.of fun i j => b i j
  let N : Matrix n n E := Matrix.of fun k j => b.repr (Pi.single k 1) j
  have hNM : N * M = 1 := by
    refine Matrix.ext fun k j => ?_
    show Matrix.vecMul (b.repr (Pi.single k 1)) M j = _
    rw [vecMul_rows_repr]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hMN : M * N = 1 := mul_eq_one_comm.2 hNM
  let qE : GL n E := ⟨M, N, hMN, hNM⟩
  let p : GL n ↥(MaximalUnramifiedExtension l) := (Matrix.GeneralLinearGroup.map ι qE)⁻¹
  have hp : (p : Matrix n n ↥(MaximalUnramifiedExtension l)) = N.map ι := by
    show ((Matrix.GeneralLinearGroup.map ι qE)⁻¹ : GL n ↥(MaximalUnramifiedExtension l)).val = _
    rw [← map_inv]
    rfl
  have hpinv : ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = M.map ι := by
    show ((Matrix.GeneralLinearGroup.map ι qE)⁻¹⁻¹ : GL n ↥(MaximalUnramifiedExtension l)).val = _
    rw [inv_inv]
    rfl
  let R : ↥(GK K) → Matrix n n E := fun g => Matrix.of fun i j => (⟨(ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j, hρ.rat g i j⟩ : E)
  have hR : ∀ g, ((ρ g : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = (R g).map ι := fun g => by
    ext i j; rfl
  refine ⟨s, p, hsne, hsuniv, fun i j => ?_, fun g i j hi hj => ?_⟩
  · rw [hp]
    exact hE (N i j)
  · rw [Units.val_mul, Units.val_mul, hpinv, hR, hp, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    suffices h : (M * R g * N) i j = 0 by rw [h, map_zero]
    show Matrix.vecMul (Matrix.vecMul (b i) (R g)) N j = 0
    rw [vecMul_repr_rows]
    have hw : Matrix.vecMul (b i) (R g) ∈ W' := by
      rw [memW']
      have h1 : cv (b i) ∈ W := hSW ((hs i).1 hi)
      have h2 := hWst g _ h1
      convert h2 using 1
      funext k
      show ι (Matrix.vecMul (b i) (R g) k) = Matrix.vecMul (cv (b i)) (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.vecMul, dotProduct, map_sum, map_mul]
      rfl
    have := (Module.Basis.mem_span_image b).1 (hWspan hw)
    by_contra hne
    exact this ((Finsupp.mem_support_iff).2 hne) (by simpa using hj)

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionActionOnFixK1
section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.GLp.red_surjective (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Function.Surjective (_root_.GlobalTheory.GLp.red g n) :=
  _root_.GlobalTheory.GLp.Model.red_surjective n

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.GLp.red_invFun (x : _root_.GlobalTheory.GLq.Gn g n) :
    _root_.GlobalTheory.GLp.red g n (Function.invFun (_root_.GlobalTheory.GLp.red g n) x) = x :=
  Function.invFun_eq (_root_.GlobalTheory.GLp.red_surjective g n x)

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.GLp.mem_principalCongruenceFixedVectors_iff (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (v : V) :
    v ∈ _root_.GlobalTheory.GLp.fixK1 π ↔ ∀ k : GL (Fin n) ℤ_[g],
      _root_.GlobalTheory.GLp.red g n k = 1 → π (_root_.GlobalTheory.GLp.inc g n k) v = v :=
  _root_.GlobalTheory.GLp.Model.mem_principalCongruenceFixedVectors_iff π v

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.GLp.padicIntGL_smul_mem_principalCongruenceFixed (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    {v : V} (hv : v ∈ _root_.GlobalTheory.GLp.fixK1 π) (a : GL (Fin n) ℤ_[g]) :
    π (_root_.GlobalTheory.GLp.inc g n a) v ∈ _root_.GlobalTheory.GLp.fixK1 π := by
  rw [_root_.GlobalTheory.GLp.mem_principalCongruenceFixedVectors_iff] at hv ⊢
  intro k hk
  have hconj : _root_.GlobalTheory.GLp.red g n (a⁻¹ * k * a) = 1 := by simp [hk]
  have h : k * a = a * (a⁻¹ * k * a) := by group
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, h, map_mul, map_mul, Module.End.mul_apply,
    hv _ hconj]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.GLp.inc_eq_of_red_eq (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    {v : V} (hv : v ∈ _root_.GlobalTheory.GLp.fixK1 π) {a b : GL (Fin n) ℤ_[g]}
    (hab : _root_.GlobalTheory.GLp.red g n a = _root_.GlobalTheory.GLp.red g n b) :
    π (_root_.GlobalTheory.GLp.inc g n a) v = π (_root_.GlobalTheory.GLp.inc g n b) v := by
  have hk : _root_.GlobalTheory.GLp.red g n (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  have hb : b = a * (a⁻¹ * b) := by group
  conv_rhs => rw [hb]
  rw [map_mul, map_mul, Module.End.mul_apply,
    (_root_.GlobalTheory.GLp.mem_principalCongruenceFixedVectors_iff π v).1 hv _ hk]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.GLp.lift_mul_apply (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V}
    (hv : v ∈ _root_.GlobalTheory.GLp.fixK1 π) (x y : _root_.GlobalTheory.GLq.Gn g n) :
    π (_root_.GlobalTheory.GLp.lift g n (x * y)) v =
      π (_root_.GlobalTheory.GLp.lift g n x) (π (_root_.GlobalTheory.GLp.lift g n y) v) := by
  obtain ⟨a, rfl⟩ := _root_.GlobalTheory.GLp.red_surjective g n x
  obtain ⟨b, rfl⟩ := _root_.GlobalTheory.GLp.red_surjective g n y
  rw [← map_mul, _root_.GlobalTheory.GLp.Model.lift_red π hv,
    _root_.GlobalTheory.GLp.Model.lift_red π hv b,
    _root_.GlobalTheory.GLp.Model.lift_red π
      (_root_.GlobalTheory.GLp.padicIntGL_smul_mem_principalCongruenceFixed π hv b) a,
    map_mul, map_mul, Module.End.mul_apply]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.GLp.lift_one_apply (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V}
    (hv : v ∈ _root_.GlobalTheory.GLp.fixK1 π) :
    π (_root_.GlobalTheory.GLp.lift g n 1) v = v := by
  rw [← map_one (_root_.GlobalTheory.GLp.red g n), _root_.GlobalTheory.GLp.Model.lift_red π hv,
    map_one, map_one, Module.End.one_apply]

theorem actK_zero (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : actK π 0 = 0 := by
  simp [actK]

theorem actK_add (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : MonoidAlgebra ℂ (Gn g n)) :
    actK π (a + b) = actK π a + actK π b := by
  simp [actK, add_smul, Finset.sum_add_distrib]

theorem actK_single (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (x : Gn g n) (c : ℂ) :
    actK π (MonoidAlgebra.single x c) = c • π (lift g n x) := by
  unfold actK
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Finsupp.single_eq_of_ne hy]
  · simp

theorem actK_mul_apply (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 π)
    (a b : MonoidAlgebra ℂ (Gn g n)) : actK π (a * b) v = actK π a (actK π b v) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp [actK_zero]
  | add a a' ha ha' => simp [add_mul, actK_add, ha, ha']
  | single x c =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp [actK_zero]
    | add b b' hb hb' => simp only [mul_add, actK_add, hb, hb', LinearMap.add_apply, map_add (f := _)]
    | single y d =>
      rw [MonoidAlgebra.single_mul_single, actK_single, actK_single, actK_single]
      simp only [LinearMap.smul_apply, map_smul, lift_mul_apply π hv, smul_smul, mul_comm]

theorem finite_group_acts_on_fixK1 :
    ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V), Function.Surjective (red g n) ∧ ∀ v ∈ fixK1 π, (∀ x, π (lift g n x) v ∈ fixK1 π) ∧ (∀ k, π (inc g n k) v = π (lift g n (red g n k)) v) ∧ (∀ x y, π (lift g n (x * y)) v = π (lift g n x) (π (lift g n y) v)) ∧ (∀ a b, actK π (a * b) v = actK π a (actK π b v)) ∧ actK π 1 v = v := by
  intro g _ n V _ _ π
  refine ⟨red_surjective g n, fun v hv => ⟨fun x => padicIntGL_smul_mem_principalCongruenceFixed π hv _,
    fun k => inc_eq_of_red_eq π hv (red_invFun _).symm, lift_mul_apply π hv, actK_mul_apply π hv, ?_⟩⟩
  rw [MonoidAlgebra.one_def, actK_single]
  simp [lift_one_apply π hv]

end GlobalTheory.GLp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScalGLCommute
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Twist

def scalGL (n : Type) [Fintype n] [DecidableEq n] {R : Type} [CommRing R] : Rˣ →* GL n R :=
  Units.map (Matrix.scalar n : R →+* Matrix n n R).toMonoidHom

theorem scalGL_val (n : Type) [Fintype n] [DecidableEq n] {R : Type} [CommRing R] (u : Rˣ) :
    ((scalGL n u : GL n R) : Matrix n n R) = Matrix.scalar n (u : R) := rfl

theorem scalGL_commute (n : Type) [Fintype n] [DecidableEq n] {R : Type} [CommRing R] (u : Rˣ) (M : GL n R) :
    Commute (scalGL n u) M :=
  Units.ext ((Matrix.scalar_commute (u : R) (fun _ => mul_comm _ _) (M : Matrix n n R)))

theorem scalGL_mul_val {n : Type} [Fintype n] [DecidableEq n] {R : Type} [CommRing R] (u : Rˣ) (M : GL n R) :
    ((scalGL n u * M : GL n R) : Matrix n n R) = (u : R) • (M : Matrix n n R) := by
  rw [Units.val_mul, scalGL_val, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

def twist {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ)
    (a : ℤ) : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l) where
  toFun g := scalGL n (χ g ^ a) * (ρ.comp (Subgroup.inclusion (GK_le hK))) g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, mul_zpow]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, (scalGL_commute n _ _).eq]

theorem twist_val {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ)
    (a : ℤ) (g : ↥(GK K')) : (twist hK ρ χ a g : Matrix n n ↥(MaximalUnramifiedExtension l)) =
      (((χ g ^ a : (↥(MaximalUnramifiedExtension l))ˣ)) : ↥(MaximalUnramifiedExtension l)) • (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) :=
  scalGL_mul_val _ _

end GlobalTheory.PMon.Twist

end
end

