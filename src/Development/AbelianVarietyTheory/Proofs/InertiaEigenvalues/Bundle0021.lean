module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubOfMemSpan
section
open TensorProduct

namespace GlobalTheory.EtaleSub

section Fixed

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : R →+* R) (Φ : M →+ M)

def fixIn (U : Submodule R M) : Set M := {x | x ∈ U ∧ Φ x = x}

theorem exists_sub_of_mem_span (hΦ : ∀ r x, Φ (r • x) = φ r • Φ x) (hs : ∀ y, ∃ b, φ b - b = y)
    (U : Submodule R M) (y : M) (hy : y ∈ Submodule.span R (fixIn Φ U)) :
    ∃ z ∈ U, Φ z - z = y := by
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hy
  choose b hb using fun i => hs (c i)
  refine ⟨∑ i, b i • (g i : M), U.sum_mem fun i _ => U.smul_mem _ (g i).2.1, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hΦ, (g i).2.2, ← sub_smul, hb]

theorem le_span_step (hΦ : ∀ r x, Φ (r • x) = φ r • Φ x) (hs : ∀ y, ∃ b, φ b - b = y)
    (hI : ∀ I : Ideal R, (∀ x ∈ I, φ x ∈ I) → I ≤ Ideal.span {x | x ∈ I ∧ φ x = x})
    (U : Submodule R M) (hU : ∀ x ∈ U, Φ x ∈ U) (f : M →ₗ[R] R) (hf : ∀ x, f (Φ x) = φ (f x))
    (h0 : U ⊓ LinearMap.ker f ≤ Submodule.span R (fixIn Φ (U ⊓ LinearMap.ker f))) :
    U ≤ Submodule.span R (fixIn Φ U) := by
  have h1 : U ⊓ LinearMap.ker f ≤ Submodule.span R (fixIn Φ U) :=
    h0.trans (Submodule.span_mono fun x hx => ⟨hx.1.1, hx.2⟩)
  have h2 : U.map f ≤ (Submodule.span R (fixIn Φ U)).map f := by
    refine (hI (U.map f) ?_).trans ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨Φ x, hU x hx, hf x⟩
    · rw [Ideal.span_le]
      rintro _ ⟨⟨u, hu, rfl⟩, hfix⟩
      have hmem : Φ u - u ∈ U ⊓ LinearMap.ker f :=
        ⟨U.sub_mem (hU u hu) hu, by
          change f (Φ u - u) = 0
          rw [map_sub, hf, hfix, sub_self]⟩
      obtain ⟨z, hz, hz'⟩ := exists_sub_of_mem_span φ Φ hΦ hs _ _ (h0 hmem)
      refine ⟨u - z, Submodule.subset_span ⟨U.sub_mem hu hz.1, ?_⟩, ?_⟩
      · rw [map_sub]
        exact sub_eq_sub_iff_sub_eq_sub.2 hz'.symm
      · have : f z = 0 := hz.2
        rw [map_sub, this, sub_zero]
  intro x hx
  obtain ⟨s, hs', hsx⟩ := h2 ⟨x, hx, rfl⟩
  have hsU : s ∈ U := (Submodule.span_le.2 fun y hy => hy.1 : Submodule.span R (fixIn Φ U) ≤ U) hs'
  have : x - s ∈ U ⊓ LinearMap.ker f := ⟨U.sub_mem hx hsU, by
    change f (x - s) = 0
    rw [map_sub, hsx, sub_self]⟩
  simpa using Submodule.add_mem _ (h1 this) hs'

theorem le_span_fixIn (hΦ : ∀ r x, Φ (r • x) = φ r • Φ x) (hs : ∀ y, ∃ b, φ b - b = y)
    (hI : ∀ I : Ideal R, (∀ x ∈ I, φ x ∈ I) → I ≤ Ideal.span {x | x ∈ I ∧ φ x = x})
    {ι : Type} [Finite ι] (f : ι → M →ₗ[R] R) (hf : ∀ i x, f i (Φ x) = φ (f i x))
    (hinj : ∀ x, (∀ i, f i x = 0) → x = 0)
    (U : Submodule R M) (hU : ∀ x ∈ U, Φ x ∈ U) : U ≤ Submodule.span R (fixIn Φ U) := by
  classical
  haveI := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, ∀ U : Submodule R M, (∀ x ∈ U, Φ x ∈ U) →
      (∀ x ∈ U, ∀ i ∉ s, f i x = 0) → U ≤ Submodule.span R (fixIn Φ U) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro U _ h x hx
      rw [hinj x fun i => h x hx i (by simp)]
      exact Submodule.zero_mem _
    | insert a s _ ih =>
      intro U hU h
      refine le_span_step φ Φ hΦ hs hI U hU (f a) (hf a) (ih _ ?_ ?_)
      · intro x hx
        refine ⟨hU x hx.1, ?_⟩
        have : f a x = 0 := hx.2
        change f a (Φ x) = 0
        rw [hf, this, map_zero]
      · intro x hx i hi
        by_cases hia : i = a
        · subst hia; exact hx.2
        · exact h x hx.1 i (by simp [hia, hi])
  exact key Finset.univ U hU fun _ _ i hi => absurd (Finset.mem_univ i) hi

end Fixed

theorem tensor_le_span {A R T : Type} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup T]
    [Module A T] [Module.Free A T] [Module.Finite A T] (φ : R →ₐ[A] R)
    (hs : ∀ y, ∃ b, φ b - b = y)
    (hI : ∀ I : Ideal R, (∀ x ∈ I, φ x ∈ I) → I ≤ Ideal.span {x | x ∈ I ∧ φ x = x})
    (U : Submodule R (R ⊗[A] T))
    (hU : ∀ x ∈ U, TensorProduct.map φ.toLinearMap LinearMap.id x ∈ U) :
    U ≤ Submodule.span R {x | x ∈ U ∧ TensorProduct.map φ.toLinearMap LinearMap.id x = x} := by
  let b := Module.Free.chooseBasis A T
  refine le_span_fixIn φ.toRingHom
    (TensorProduct.map φ.toLinearMap (LinearMap.id : T →ₗ[A] T)).toAddMonoidHom ?_ hs hI
    (fun i => (b.baseChange R).coord i) ?_ ?_ U hU
  · intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  · intro i x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x hx
    exact (b.baseChange R).ext_elem fun i => by simpa using hx i

theorem ideal_le_span {A W O : Type} [CommRing A] [CommRing W] [Algebra A W] [CommRing O]
    [Algebra A O] [Module.Free A O] [Module.Finite A O] (φ : W →ₐ[A] W)
    (hs : ∀ y, ∃ b, φ b - b = y)
    (hI : ∀ I : Ideal W, (∀ x ∈ I, φ x ∈ I) → I ≤ Ideal.span {x | x ∈ I ∧ φ x = x})
    (I : Ideal (O ⊗[A] W)) (hU : ∀ x ∈ I, Algebra.TensorProduct.map (AlgHom.id O O) φ x ∈ I) :
    I ≤ Ideal.span {x | x ∈ I ∧ Algebra.TensorProduct.map (AlgHom.id O O) φ x = x} := by
  let e := Algebra.TensorProduct.comm A W O
  have hc : ∀ b : W ⊗[A] O, e (TensorProduct.map φ.toLinearMap LinearMap.id b) =
      Algebra.TensorProduct.map (AlgHom.id O O) φ (e b) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul a w => simp [e]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let U : Submodule W (W ⊗[A] O) := (I.comap e.toRingEquiv.toRingHom).restrictScalars W
  have hUm : ∀ x, x ∈ U ↔ e x ∈ I := fun x => Iff.rfl
  have h := tensor_le_span φ hs hI U fun x hx => by
    rw [hUm, hc]; exact hU _ hx
  intro x hx
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy := h ((hUm y).2 hx)
  clear hx
  induction hy using Submodule.span_induction with
  | mem z hz => exact Ideal.subset_span ⟨hz.1, by rw [← hc, hz.2]⟩
  | zero => simp
  | add z w _ _ hz hw => rw [map_add (f := _)]; exact Ideal.add_mem _ hz hw
  | smul a z _ hz => rw [Algebra.smul_def, map_mul]; exact Ideal.mul_mem_left _ _ hz

theorem flat_of_letters {E M ι : Type} [CommRing E] [AddCommGroup M] [Module E M] [Fintype ι]
    (e : ι → E) (he : ∑ i, e i = 1) (hid : ∀ i, e i * e i = e i) (ϖ : E)
    (hS : ∀ i x, e i * x = 0 ∨ ∃ (k : ℕ) (u : E), IsUnit u ∧ e i * x = e i * ϖ ^ k * u)
    (hM : ∀ m : M, ϖ • m = 0 → m = 0) : Module.Flat E M := by
  classical
  have hMk : ∀ (k : ℕ) (m : M), ϖ ^ k • m = 0 → m = 0 := by
    intro k
    induction k with
    | zero => intro m h; simpa using h
    | succ k ih => intro m h; rw [pow_succ, mul_smul] at h; exact hM _ (ih _ h)
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  have key : ∀ i, e i • t = 0 := by
    intro i
    by_cases h : ∃ k : ℕ, e i * ϖ ^ k ∈ I
    · let d : I := ⟨e i * ϖ ^ Nat.find h, Nat.find_spec h⟩
      have h1 : ∀ s : I ⊗[E] M, ∃ m : M, e i • s = d ⊗ₜ m := by
        intro s
        induction s using TensorProduct.induction_on with
        | zero => exact ⟨0, by simp⟩
        | tmul a m =>
          rw [TensorProduct.smul_tmul']
          rcases hS i a with h0 | ⟨k, u, hu, hk⟩
          · have : e i • a = 0 := Subtype.ext h0
            exact ⟨0, by rw [this]; simp⟩
          · have hk' : e i * ϖ ^ k ∈ I := by
              rw [← Ideal.mul_unit_mem_iff_mem I hu, ← hk]
              exact I.mul_mem_left _ a.2
            obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.find_min' h hk')
            have : e i • a = (ϖ ^ j * u) • d := Subtype.ext (by
              change e i * a = ϖ ^ j * u * (e i * ϖ ^ Nat.find h)
              rw [hk]; ring)
            exact ⟨(ϖ ^ j * u) • m, by rw [this, TensorProduct.smul_tmul]⟩
        | add x y hx hy =>
          obtain ⟨m, hm⟩ := hx
          obtain ⟨m', hm'⟩ := hy
          exact ⟨m + m', by rw [smul_add, hm, hm', TensorProduct.tmul_add]⟩
      obtain ⟨m, hm⟩ := h1 t
      have h2 : (d : E) • m = 0 := by
        have := congrArg (TensorProduct.lift ((LinearMap.lsmul E M).comp I.subtype)) hm
        rw [map_smul, ht, smul_zero] at this
        simpa using this.symm
      have h3 : e i • m = 0 := hMk (Nat.find h) _ (by rw [← mul_smul, mul_comm]; exact h2)
      have h4 : d = e i • d := Subtype.ext (by
        change e i * ϖ ^ Nat.find h = e i * (e i * ϖ ^ Nat.find h)
        rw [← mul_assoc, hid])
      rw [hm, h4, TensorProduct.smul_tmul, h3, TensorProduct.tmul_zero]
    · clear ht
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a m =>
        rw [TensorProduct.smul_tmul']
        rcases hS i a with h0 | ⟨k, u, hu, hk⟩
        · have : e i • a = 0 := Subtype.ext h0
          rw [this]; simp
        · refine absurd ⟨k, ?_⟩ h
          rw [← Ideal.mul_unit_mem_iff_mem I hu, ← hk]
          exact I.mul_mem_left _ a.2
      | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  rw [← one_smul E t, ← he, Finset.sum_smul]
  exact Finset.sum_eq_zero fun i _ => key i

theorem mem_of_mem_span_image {E R D M : Type} [CommRing E] [CommRing R] [Algebra E R]
    [Module.FaithfullyFlat E R] [AddCommGroup D]
    [Module E D] [AddCommGroup M] [Module R M] [Module.Free E D] [Module.Finite E D]
    (j : D →+ M) (hj : ∀ e x, j (e • x) = algebraMap E R e • j x)
    (hrank : Nontrivial R → Module.finrank E D = Module.finrank R M)
    (hspan : Submodule.span R (Set.range j) = ⊤)
    (N : Submodule E D) (x : D) (hx : j x ∈ Submodule.span R (j '' (N : Set D))) : x ∈ N := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · haveI := Module.subsingleton E D
    rw [Subsingleton.elim x 0]; exact N.zero_mem
  haveI : Nontrivial R := (FaithfulSMul.algebraMap_injective E R).nontrivial
  let b := Module.Free.chooseBasis E D
  have hsp : ⊤ ≤ Submodule.span R (Set.range fun i => j (b i)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hj]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c := basisOfTopLeSpanOfCardEqFinrank (fun i => j (b i)) hsp
    (by rw [← hrank inferInstance, Module.finrank_eq_card_chooseBasisIndex])
  have hc : ∀ i, c i = j (b i) := fun i => by simp [c]
  let F : M →ₗ[R] R ⊗[E] (D ⧸ N) := c.constr R fun i => (1 : R) ⊗ₜ N.mkQ (b i)
  have hF : ∀ x, F (j x) = (1 : R) ⊗ₜ N.mkQ x := by
    intro x
    rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hj, map_smul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc, Module.Basis.constr_basis, algebraMap_smul, TensorProduct.tmul_smul]
  have hker : Submodule.span R (j '' (N : Set D)) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    change F (j y) = 0
    rw [hF, show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero _).2 hy, TensorProduct.tmul_zero]
  have h1 : (1 : R) ⊗ₜ[E] N.mkQ x = 0 := (hF x).symm.trans (hker hx)
  exact (Submodule.Quotient.mk_eq_zero _).1
    ((Module.FaithfullyFlat.one_tmul_eq_zero_iff E (D ⧸ N) _).1 h1)

end GlobalTheory.EtaleSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueAlgHomOfPadicLocalization
section
open PowerSeries

namespace GlobalTheory

theorem existsUnique_algHom_of_padic_localization {O A E B : Type} [CommRing O] [CommRing A]
    [CommRing E] [CommRing B] [Algebra O A] [Algebra O E] [Algebra O B] (p : ℕ) (x : A)
    (ι : A →ₐ[O] E) (f : A →ₐ[O] B) (_hι : IsUnit (ι x)) (hf : IsUnit (f x))
    (hB : IsAdicComplete (Ideal.span {(p : B)}) B)
    (hd : ∀ (y : E) (k : ℕ), ∃ (a : A) (m : ℕ), (p : E) ^ k ∣ y * ι (x ^ m) - ι a)
    (hi : ∀ (a : A) (k : ℕ), (p : E) ^ k ∣ ι a → (p : A) ^ k ∣ a) :
    ∃! g : E →ₐ[O] B, ∀ a, g (ι a) = f a := by
  obtain ⟨v, hv⟩ := hf.exists_right_inv
  have hvm : ∀ m : ℕ, f x ^ m * v ^ m = 1 := fun m => by rw [← mul_pow, hv, one_pow]
  have smod : ∀ (k : ℕ) (z w : B),
      z ≡ w [SMOD ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B)] ↔ (p : B) ^ k ∣ z - w := by
    intro k z w
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have ext : ∀ z w : B, (∀ k, (p : B) ^ k ∣ z - w) → z = w := by
    intro z w h
    have := IsHausdorff.haus hB.toIsHausdorff (z - w) (fun k => by
      rw [smod, sub_zero]; exact h k)
    exact sub_eq_zero.mp this
  have key : ∀ (y : E) (k : ℕ) (a : A) (m : ℕ) (a' : A) (m' : ℕ),
      (p : E) ^ k ∣ y * ι (x ^ m) - ι a → (p : E) ^ k ∣ y * ι (x ^ m') - ι a' →
      (p : B) ^ k ∣ f a * v ^ m - f a' * v ^ m' := by
    intro y k a m a' m' h h'
    have h1 : (p : E) ^ k ∣ ι (a * x ^ m' - a' * x ^ m) := by
      have : ι (a * x ^ m' - a' * x ^ m) =
          ι (x ^ m) * (y * ι (x ^ m') - ι a') - ι (x ^ m') * (y * ι (x ^ m) - ι a) := by
        simp only [map_sub, map_mul]; ring
      rw [this]
      exact dvd_sub (h'.mul_left _) (h.mul_left _)
    have h2 := map_dvd f (hi _ _ h1)
    simp only [map_pow, map_natCast, map_sub, map_mul] at h2
    have : f a * v ^ m - f a' * v ^ m' =
        (f a * f x ^ m' - f a' * f x ^ m) * (v ^ m * v ^ m') := by
      linear_combination (-(f a * v ^ m)) * hvm m' + (f a' * v ^ m') * hvm m
    rw [this]
    exact h2.mul_right _
  have ex : ∀ y : E, ∃ z : B, ∀ (k : ℕ) (a : A) (m : ℕ),
      (p : E) ^ k ∣ y * ι (x ^ m) - ι a → (p : B) ^ k ∣ z - f a * v ^ m := by
    intro y
    choose a m ham using hd y
    obtain ⟨z, hz⟩ := IsPrecomplete.prec hB.toIsPrecomplete
      (f := fun k => f (a k) * v ^ (m k)) (fun {j k} hjk => by
        rw [smod]
        exact key y j _ _ _ _ (ham j) ((pow_dvd_pow _ hjk).trans (ham k)))
    refine ⟨z, fun k a' m' h => ?_⟩
    have h1 := (smod _ _ _).mp (hz k)
    have h2 := key y k _ _ _ _ (ham k) h
    have := dvd_sub h2 h1
    convert this using 1
    ring
  choose g hg using ex
  have hgι : ∀ a, g (ι a) = f a := by
    intro a
    refine ext _ _ fun k => ?_
    simpa using hg (ι a) k a 0 (by simp)
  have hadd : ∀ y y', g (y + y') = g y + g y' := by
    intro y y'
    refine ext _ _ fun k => ?_
    obtain ⟨a, m, h⟩ := hd y k
    obtain ⟨a', m', h'⟩ := hd y' k
    have h1 := hg (y + y') k (a * x ^ m' + a' * x ^ m) (m + m') (by
      have := dvd_add (h.mul_left (ι (x ^ m'))) (h'.mul_left (ι (x ^ m)))
      convert this using 1
      simp only [map_add (f := _), map_mul, map_pow]; ring)
    have := dvd_sub (dvd_sub h1 (hg y k a m h)) (hg y' k a' m' h')
    convert this using 1
    simp only [map_add (f := _), map_mul, map_pow, pow_add]
    linear_combination (f a * v ^ m) * hvm m' + (f a' * v ^ m') * hvm m
  have hmul : ∀ y y', g (y * y') = g y * g y' := by
    intro y y'
    refine ext _ _ fun k => ?_
    obtain ⟨a, m, h⟩ := hd y k
    obtain ⟨a', m', h'⟩ := hd y' k
    have h1 := hg (y * y') k (a * a') (m + m') (by
      have := dvd_add (h.mul_left (y' * ι (x ^ m'))) (h'.mul_left (ι a))
      convert this using 1
      simp only [map_add (f := _), map_mul, map_pow]; ring)
    have := dvd_sub (dvd_sub h1 ((hg y k a m h).mul_left (g y')))
      ((hg y' k a' m' h').mul_left (f a * v ^ m))
    convert this using 1
    simp only [map_add (f := _), map_mul, map_pow, pow_add]
    ring
  refine ⟨
    { toFun := g
      map_one' := by simpa using hgι 1
      map_mul' := hmul
      map_zero' := by simpa using hgι 0
      map_add' := hadd
      commutes' := fun r => by simpa using hgι (algebraMap O A r) }, hgι, ?_⟩
  intro g' hg'
  ext y
  refine ext _ _ fun k => ?_
  obtain ⟨a, m, h⟩ := hd y k
  have h1 := map_dvd g' h
  rw [map_sub, map_mul, hg', hg', map_pow, map_natCast, map_pow] at h1
  have := dvd_sub (h1.mul_right (v ^ m)) (hg y k a m h)
  convert this using 1
  show g' y - g y = _
  linear_combination (-(g' y)) * hvm m

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEq
section
namespace GlobalTheory.FrobeniusProduct

theorem exists_adic_limit {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A]
    (s : ℕ → A) (hs : ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r) :
    ∃ L : A, ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s m - L ∈ I ^ r := by
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  choose N hN using hs
  have tele : ∀ r a b, (∀ k ≥ a, s (k + 1) - s k ∈ I ^ r) → a ≤ b → s b - s a ∈ I ^ r := by
    intro r a b h hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have := (I ^ r).add_mem (h b hab) ih
      convert this using 1
      ring
  set N' : ℕ → ℕ := fun r => ∑ j ∈ Finset.range (r + 1), N j with hN'
  have hN'ge : ∀ r, N r ≤ N' r := fun r =>
    Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le _) (Finset.self_mem_range_succ r)
  have hN'mono : Monotone N' := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance
    (f := fun r => s (N' r)) (by
      intro m n hmn
      rw [SModEq.sub_mem, hsm]
      have := tele m (N' m) (N' n) (fun k hk => hN m k (le_trans (hN'ge m) hk)) (hN'mono hmn)
      have := (I ^ m).neg_mem this
      simpa using this)
  refine ⟨L, fun r => ⟨N' r, fun m hm => ?_⟩⟩
  have h1 := tele r (N' r) m (fun k hk => hN r k (le_trans (hN'ge r) hk)) hm
  have h2 : s (N' r) - L ∈ I ^ r := by
    have := hL r
    rw [SModEq.sub_mem, hsm] at this
    exact this
  have := (I ^ r).add_mem h1 h2
  convert this using 1
  ring

theorem exists_unit_iterate_mul_eq :
    ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A →
      ∀ (φ : A →+* A) (u : A), IsUnit u →
        (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) →
          ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  intro A _ p hc φ u hu hconv n hn
  haveI := hc
  set I : Ideal A := Ideal.span {(p : A)} with hI
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  obtain ⟨w, hw⟩ : ∃ w : ℕ → A, w = fun k => (⇑φ)^[n * k + (n - 1)] u := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → A, s = fun N => ∏ k ∈ Finset.range N, w k := ⟨_, rfl⟩
  have hwconv : ∀ r, ∃ M, ∀ k ≥ M, w k - 1 ∈ I ^ r := fun r => by
    obtain ⟨M, hM⟩ := hconv r
    exact ⟨M, fun k hk => by rw [hw]; exact hM _ (by nlinarith)⟩
  have hcauchy : ∀ r, ∃ N, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r := by
    intro r
    obtain ⟨M, hM⟩ := hwconv r
    refine ⟨M, fun m hm => ?_⟩
    have e : s (m + 1) - s m = s m * (w m - 1) := by
      simp only [hs, Finset.prod_range_succ]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (hM m hm)
  obtain ⟨c, hc'⟩ := exists_adic_limit I s hcauchy
  have haus : ∀ x : A, (∀ r : ℕ, x ∈ I ^ r) → x = 0 := fun x hx =>
    IsHausdorff.haus (I := I) (M := A) inferInstance x (fun r => by rw [SModEq.zero, hsm]; exact hx r)
  have hmap : ∀ k (x : A) r, x ∈ I ^ r → (⇑φ)^[k] x ∈ I ^ r := by
    intro k x r hx
    have := Ideal.mem_map_of_mem (φ ^ k) hx
    rwa [Ideal.map_pow, hI, Ideal.map_span, Set.image_singleton, map_natCast,
      RingHom.coe_pow] at this
  have hsub : ∀ x y : A, (⇑φ)^[n] (x - y) = (⇑φ)^[n] x - (⇑φ)^[n] y := by
    intro x y; rw [← RingHom.coe_pow]; exact map_sub _ _ _
  have key : ∀ N, (⇑φ)^[n] (s N) * (⇑φ)^[n - 1] u = s (N + 1) := by
    intro N
    simp only [hs, Finset.prod_range_succ']
    rw [← RingHom.coe_pow, map_prod]
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      simp only [RingHom.coe_pow, hw]
      rw [← Function.iterate_add_apply]
      congr 1
      ring
    · simp [hw]
  have hwunit : ∀ k, IsUnit (w k) := fun k => by
    rw [hw]; show IsUnit ((⇑φ)^[n * k + (n - 1)] u)
    rw [← RingHom.coe_pow]; exact hu.map _
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hc' 1
    have h1 : s N - c ∈ I := by simpa using hN N le_rfl
    have hsN : IsUnit (s N) := by
      rw [hs]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun k _ => hwunit k)
    obtain ⟨v, hv⟩ := hsN
    have hy : -(s N - c) ∈ (⊥ : Ideal A).jacobson :=
      IsAdicComplete.le_jacobson_bot I (I.neg_mem h1)
    have hu' := (Ideal.mem_jacobson_bot.mp hy) (↑v⁻¹ : A)
    have heq : c = (-(s N - c) * (↑v⁻¹ : A) + 1) * ↑v := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hv]; ring
    rw [heq]
    exact hu'.mul v.isUnit
  · refine sub_eq_zero.mp (haus _ fun r => ?_)
    obtain ⟨N, hN⟩ := hc' r
    have e : (⇑φ)^[n] c * (⇑φ)^[n - 1] u - c =
        -((⇑φ)^[n] (s N - c) * (⇑φ)^[n - 1] u) + (s (N + 1) - c) := by
      rw [← key N, hsub]; ring
    rw [e]
    exact (I ^ r).add_mem ((I ^ r).neg_mem (Ideal.mul_mem_right _ _ (hmap n _ r (hN N le_rfl))))
      (hN (N + 1) (by omega))

end GlobalTheory.FrobeniusProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixMulEntryNormLeUltrametric
section
namespace GlobalTheory

theorem matrix_mul_entry_norm_le_ultrametric :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (A B : Matrix n n E) (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ i j, ‖A i j‖ ≤ a) → (∀ i j, ‖B i j‖ ≤ b) →
      ∀ i j, ‖(A * B) i j‖ ≤ a * b := by
  intro E _ _ n _ _ A B a b ha hb hA hB i j
  rw [Matrix.mul_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb)
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha

end GlobalTheory
end

