module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.InvEv
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.invEv :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), l ≠ 2 → ∀ Y : Matrix (Fin n) (Fin n) x.Fr, Y ∈ Ev x.A x.Fr n x.a → Yᵀ = -Y → (∀ g : G.G₀, dY G.frame (fun g => x.ρX x.Fr (h.p₀ g)) Y g = 0) → Y = 0 := by
  intro l hl L G G0 h n x hl2 Y _ hT hd
  have hmul : ∀ g g', x.ρX x.Fr (g * g') = x.ρX x.Fr g * x.ρX x.Fr g' := by
    intro g g'
    simp only [NP.ρX, mat, map_mul, Units.val_mul]
    exact Matrix.map_mul
  have hone : x.ρX x.Fr 1 = 1 := by
    simp only [NP.ρX, mat, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hsurj : Function.Surjective h.p₀ := by
    intro g
    obtain ⟨γ, hγ⟩ := h.surj g.1
    have hm : γ ∈ G.η.ker := by
      rw [MonoidHom.mem_ker, ← h.η γ, hγ]
      exact g.2
    exact ⟨⟨γ, hm⟩, Subtype.ext hγ⟩
  have hc : ∀ g, x.ρX x.Fr g * Y = Y * x.ρX x.Fr g := by
    intro g
    obtain ⟨γ, rfl⟩ := hsurj g
    have e := hd γ
    simp only [dY, sub_eq_zero] at e
    have e2 : x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ) = 1 := by
      rw [← hmul, ← map_mul, inv_mul_cancel, map_one, hone]
    calc x.ρX x.Fr (h.p₀ γ) * Y
        = x.ρX x.Fr (h.p₀ γ) * Y * (x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ)) := by rw [e2, mul_one]
      _ = Y * x.ρX x.Fr (h.p₀ γ) := by rw [← mul_assoc, e]
  have hs : ∀ Z ∈ Submodule.span x.A (mat x.ρ '' (G0.frame.G' : Set G0.frame.G₀)),
      Z.map (algebraMap x.A x.Fr) * Y = Y * Z.map (algebraMap x.A x.Fr) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, _, rfl⟩ := hZ
      exact hc g
    | zero => simp
    | add a b _ _ ha hb =>
      rw [Matrix.map_add _ (map_add _), add_mul, mul_add, ha, hb]
    | smul c a _ ha =>
      have : (c • a).map (algebraMap x.A x.Fr) = algebraMap x.A x.Fr c • a.map (algebraMap x.A x.Fr) := by
        ext i j; simp
      rw [this, Matrix.smul_mul, Matrix.mul_smul, ha]
  have h2 : (2 : x.Fr) ≠ 0 := by
    have hu : IsUnit (2 : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      have : ¬ ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        intro hdv
        have : l ∣ 2 := by exact_mod_cast hdv
        exact hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 this)
      have h3 : ‖((2 : ℤ) : ℤ_[l])‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.1 this)
      simpa using h3
    have := (hu.map (((algebraMap x.A x.Fr).comp (algebraMap x.K x.A)).comp (algebraMap ℤ_[l] x.K))).ne_zero
    rwa [map_ofNat] at this
  ext i j
  by_cases hij : i = j
  · subst hij
    have e := congrFun (congrFun hT i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at e
    have : (2 : x.Fr) * Y i i = 0 := by linear_combination e
    simpa using (mul_eq_zero.1 this).resolve_left h2
  · have hE : (Matrix.single i i (1 : x.A)) ∈ Ev x.A x.A n x.a := by
      intro p q
      refine ⟨fun _ => trivial, fun hne => ?_⟩
      rw [Submodule.mem_bot]
      apply Matrix.single_apply_of_ne
      rintro ⟨rfl, rfl⟩
      exact hne Iff.rfl
    obtain ⟨s, hsp⟩ := x.span _ hE
    have e := hs _ hsp
    have hm : ((PowerSeries.X : PowerSeries x.K) ^ s • Matrix.single i i (1 : x.A)).map (algebraMap x.A x.Fr)
        = Matrix.single i i (algebraMap x.A x.Fr (x.t ^ s)) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.map_single]
    rw [hm] at e
    have e' := congrFun (congrFun e i) j
    rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hij)] at e'
    have ht : algebraMap x.A x.Fr (x.t ^ s) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact pow_ne_zero _ PowerSeries.X_ne_zero
    simpa using (mul_eq_zero.1 e').resolve_left ht
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Ired
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.aaCO :
    ∀ (O B A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] [CommRing A] [Algebra B A] [Module.Finite B A] (N : Submodule B A), Function.Injective (algebraMap B A) → _root_.IsCompl (1 : Submodule B A) N → (∀ a ∈ N, ∀ b ∈ N, ∃ c ∈ maximalIdeal B, a * b = algebraMap B A c) → ∀ [Algebra O A] [IsScalarTower O B A], ∃ _ : IsCO O A, (∀ a, a ∈ maximalIdeal A ↔ a ∈ (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A)) ∧ (ired N).map (algebraMap B A) ≤ maximalIdeal A ^ 2 := by
  intro O B A _ _ _ _ _ _ _ _ _ _ N hinj hc hN _ _
  have hdec : ∀ a : A, ∃ b : B, ∃ n ∈ N, a = algebraMap B A b + n := by
    intro a
    have ha : a ∈ (1 : Submodule B A) ⊔ N := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, n, hn, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hu
    exact ⟨b, n, hn, rfl⟩
  let S : Set A := {a | ∃ b ∈ maximalIdeal B, ∃ n ∈ N, a = algebraMap B A b + n}
  have hSmul : ∀ x a, a ∈ S → x * a ∈ S := by
    rintro x a ⟨b, hb, n, hn, rfl⟩
    obtain ⟨b', n', hn', rfl⟩ := hdec x
    obtain ⟨c, hc', hcn⟩ := hN n' hn' n hn
    refine ⟨b' * b + c, Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb) hc', b' • n + b • n',
      N.add_mem (N.smul_mem _ hn) (N.smul_mem _ hn'), ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_add (f := _), map_mul, ← hcn]
    ring
  have hSadd : ∀ a a', a ∈ S → a' ∈ S → a + a' ∈ S := by
    rintro a a' ⟨b, hb, n, hn, rfl⟩ ⟨b', hb', n', hn', rfl⟩
    exact ⟨b + b', Ideal.add_mem _ hb hb', n + n', N.add_mem hn hn', by rw [map_add (f := _)]; ring⟩
  have h1 : (1 : A) ∉ S := by
    rintro ⟨b, hb, n, hn, e⟩
    have hn1 : n ∈ (1 : Submodule B A) :=
      Submodule.mem_one.mpr ⟨1 - b, by rw [map_sub, map_one, e]; ring⟩
    have hn0 : n = 0 := by
      have hmem : n ∈ (1 : Submodule B A) ⊓ N := ⟨hn1, hn⟩
      rw [hc.inf_eq_bot] at hmem
      exact (Submodule.mem_bot B).mp hmem
    rw [hn0, add_zero, ← map_one (algebraMap B A)] at e
    have hb1 := hinj e
    rw [← hb1] at hb
    exact (IsLocalRing.mem_maximalIdeal _).mp hb isUnit_one
  have hnon : ∀ a : A, a ∈ S → ¬IsUnit a := by
    rintro a ha ⟨u, rfl⟩
    apply h1
    have := hSmul (↑u⁻¹) _ ha
    rwa [Units.inv_mul] at this
  have hunit : ∀ a : A, a ∉ S → IsUnit a := by
    intro a ha
    obtain ⟨b, n, hn, rfl⟩ := hdec a
    have hb : b ∉ maximalIdeal B := fun hb => ha ⟨b, hb, n, hn, rfl⟩
    obtain ⟨c, hcm, hcn⟩ := hN n hn n hn
    have hu : IsUnit (b * b - c) := by
      by_contra h
      apply hb
      have h' : b * b - c ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr h
      have hbb : b * b ∈ maximalIdeal B := by simpa using Ideal.add_mem _ h' hcm
      exact ((IsLocalRing.maximalIdeal.isMaximal B).isPrime.mem_or_mem hbb).elim id id
    have hprod : (algebraMap B A b + n) * (algebraMap B A b - n) = algebraMap B A (b * b - c) := by
      rw [map_sub, map_mul, ← hcn]
      ring
    exact isUnit_of_mul_isUnit_left (by rw [hprod]; exact hu.map _)
  haveI : Nontrivial A := hinj.nontrivial
  haveI hloc : IsLocalRing A := by
    apply IsLocalRing.of_nonunits_add
    intro a a' ha ha'
    have hS' : ∀ x : A, x ∈ nonunits A → x ∈ S := fun x hx => by
      by_contra h
      exact hx (hunit x h)
    exact hnon _ (hSadd _ _ (hS' _ ha) (hS' _ ha'))
  have hmemS : ∀ a : A, a ∈ maximalIdeal A ↔ a ∈ S := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by by_contra h'; exact h (hunit a h'), hnon a⟩
  have hM : ∀ a : A, a ∈ S ↔ a ∈ (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A) := by
    intro a
    constructor
    · rintro ⟨b, hb, n, hn, rfl⟩
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hb))
        (Ideal.mem_sup_right (Ideal.subset_span hn))
    · intro ha
      refine (hmemS a).mp ?_
      have hle : (maximalIdeal B).map (algebraMap B A) ⊔ Ideal.span (N : Set A) ≤ maximalIdeal A := by
        refine sup_le (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) (Ideal.span_le.mpr fun n hn => ?_)
        · exact (hmemS _).mpr ⟨b, hb, 0, N.zero_mem, by simp⟩
        · exact (hmemS _).mpr ⟨0, zero_mem _, n, hn, by simp⟩
      exact hle ha
  haveI hco : IsCO O A := co_finite O B A (fun x => by
    obtain ⟨b, n, hn, rfl⟩ := hdec x
    obtain ⟨o, ho⟩ := IsCO.res_surj (O := O) b
    refine ⟨o, (hmemS _).mpr ⟨b - algebraMap O B o, ho, n, hn, ?_⟩⟩
    rw [IsScalarTower.algebraMap_apply O B A, map_sub]
    ring)
  refine ⟨hco, fun a => (hmemS a).trans (hM a), ?_⟩
  refine Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr ?_)
  rintro b ⟨x, hx, y, hy, e⟩
  show algebraMap B A b ∈ maximalIdeal A ^ 2
  rw [← e, pow_two]
  exact Ideal.mul_mem_mul ((hmemS x).mpr ⟨0, zero_mem _, x, hx, by simp⟩)
    ((hmemS y).mpr ⟨0, zero_mem _, y, hy, by simp⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.KapF
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.indF :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ c : Fin k.g → x.Fr, ∑ j, c j • kapF h k j ∈ BdM h x x.Fr → c = 0 := by
  intro l _ L G G0 h n x k c hc
  classical
  obtain ⟨Y, hY, hYt, hcY⟩ := hc
  have hinj : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective x.A x.Fr
  have hsurj : Function.Surjective h.p₀ := by
    rintro ⟨g', hg'⟩
    obtain ⟨γ, hγ⟩ := h.surj g'
    refine ⟨⟨γ, ?_⟩, Subtype.ext hγ⟩
    show G.η γ = 1
    rw [← h.η, hγ]
    exact hg'
  have hb : ∃ b : nonZeroDivisors x.A, ∀ i : Fin k.g ⊕ (Fin n × Fin n),
      ∃ r : x.A, algebraMap x.A x.Fr r = (b : x.A) • Sum.elim c (fun p => Y p.1 p.2) i :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors x.A) _
  obtain ⟨b, hb⟩ := hb
  choose a ha using hb
  let cA : Fin k.g → x.A := fun j => a (Sum.inl j)
  let YA : Matrix (Fin n) (Fin n) x.A := fun i j => a (Sum.inr (i, j))
  let ψ := (Algebra.ofId x.A x.Fr).mapMatrix (m := Fin n)
  have hψ : ∀ M : Matrix (Fin n) (Fin n) x.A, ψ M = M.map (algebraMap x.A x.Fr) := fun M => rfl
  have hψinj : Function.Injective ψ := by
    intro M N hMN
    refine Matrix.ext fun i j => ?_
    apply hinj
    have := congrFun (congrFun hMN i) j
    rwa [hψ, hψ] at this
  have hψY : ψ YA = (b : x.A) • Y := by
    refine Matrix.ext fun i j => ?_
    rw [hψ]
    exact ha (Sum.inr (i, j))
  have hρ : ∀ g, ψ (x.ρX x.A g) = x.ρX x.Fr g := by
    intro g
    refine Matrix.ext fun i j => ?_
    simp [hψ, NP.ρX]
  have hκ : ∀ j γ, ψ (k.κ j (h.p₀ γ)) = kapF h k j γ := fun j γ => rfl
  have hcj : ∀ j (M : Matrix (Fin n) (Fin n) x.Fr), cA j • M = (b : x.A) • (c j • M) := by
    intro j M
    rw [← algebraMap_smul x.Fr (cA j) M, ha (Sum.inl j), Sum.elim_inl, smul_assoc]
  have hmem : ∑ j, cA j • k.κ j ∈ Bd G0.frame (x.ρX x.A) (Od x.A x.A n x.a) := by
    refine ⟨YA, ?_, ?_, ?_⟩
    · intro i j
      refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
      have h0 : Y i j = 0 := (Submodule.mem_bot _).1 ((hY i j).1 hij)
      rw [Submodule.mem_bot]
      apply hinj
      rw [map_zero]
      have := ha (Sum.inr (i, j))
      rw [Sum.elim_inr, h0, smul_zero] at this
      exact this
    · refine Matrix.ext fun i j => ?_
      apply hinj
      have h1 := ha (Sum.inr (j, i))
      have h2 := ha (Sum.inr (i, j))
      rw [Sum.elim_inr] at h1 h2
      have hYij : Y j i = - Y i j := congrFun (congrFun hYt i) j
      rw [Matrix.transpose_apply, Matrix.neg_apply, map_neg]
      show algebraMap x.A x.Fr (a (Sum.inr (j, i))) = -algebraMap x.A x.Fr (a (Sum.inr (i, j)))
      rw [h1, h2, hYij, smul_neg]
    · funext g'
      obtain ⟨γ, rfl⟩ := hsurj g'
      apply hψinj
      have hL : ψ ((∑ j, cA j • k.κ j) (h.p₀ γ)) = (b : x.A) • (∑ j, c j • kapF h k j) γ := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, hκ, hcj, Finset.smul_sum]
      rw [hL, hcY]
      simp only [dY, map_sub, map_mul, hρ, hψY, Matrix.mul_smul, Matrix.smul_mul, smul_sub, map_inv]
  have hzero := k.indep cA hmem
  funext j
  have hj := ha (Sum.inl j)
  have h0 : cA j = 0 := congrFun hzero j
  rw [Sum.elim_inl, Algebra.smul_def] at hj
  change algebraMap x.A x.Fr (cA j) = _ at hj
  rw [h0, map_zero] at hj
  have hb0 : algebraMap x.A x.Fr (b : x.A) ≠ 0 := fun h0' =>
    nonZeroDivisors.ne_zero b.2 (hinj (h0'.trans (map_zero _).symm))
  exact (mul_eq_zero.1 hj.symm).resolve_left hb0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LaDual
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

open scoped TensorProduct in
private theorem UpperTheory.V.Pa.dual_functionals_finite_separating_surjective {R F N : Type} [CommRing R] [Field F] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (φ : R →+* F) (hs : Function.Surjective φ) (L : Submodule F (N →+ F))
    (hL : ∀ μ, μ ∈ L ↔ ∀ (b : R) y, μ (b • y) = φ b * μ y) :
    Module.Finite F L ∧ (∀ y : N, (∀ μ ∈ L, μ y = 0) → y ∈ RingHom.ker φ • (⊤ : Submodule R N)) ∧
      ∀ ξ : Module.Dual F L, ∃ y : N, ∀ μ : L, (μ : N →+ F) y = ξ μ := by
  classical
  have hzero : ∀ μ ∈ L, ∀ t : Set N, Submodule.span R t = ⊤ → (∀ y ∈ t, μ y = 0) → μ = 0 := by
    intro μ hμ t ht h0
    refine AddMonoidHom.ext fun y => ?_
    show μ y = 0
    have hy : y ∈ Submodule.span R t := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact h0 x hx
    | zero => exact map_zero μ
    | add x z _ _ hx hz => rw [map_add (f := _), hx, hz, add_zero]
    | smul b x _ hx => rw [(hL μ).1 hμ b x, hx, mul_zero]
  have hfin : Module.Finite F L := by
    obtain ⟨n, s, hsp⟩ := Module.Finite.exists_fin (R := R) (M := N)
    let Φ : L →ₗ[F] (Fin n → F) :=
      { toFun := fun μ i => (μ : N →+ F) (s i)
        map_add' := fun μ ν => by ext i; rfl
        map_smul' := fun c μ => by ext i; rfl }
    refine Module.Finite.of_injective Φ ?_
    refine (injective_iff_map_eq_zero Φ).2 fun μ hμ => Subtype.ext ?_
    refine hzero _ μ.2 _ hsp ?_
    rintro _ ⟨i, rfl⟩
    exact congrFun hμ i
  have hkill : ∀ y : N, (∀ μ ∈ L, μ y = 0) → y ∈ RingHom.ker φ • (⊤ : Submodule R N) := by
    intro y hy
    by_contra hny
    set K := RingHom.ker φ
    set P := K • (⊤ : Submodule R N)
    have ht : Module.IsTorsionBySet R (N ⧸ P) (K : Set R) :=
      (Module.isTorsionBySet_quotient_iff P _).2 fun x r hr =>
        Submodule.smul_mem_smul hr Submodule.mem_top
    letI : Module (R ⧸ K) (N ⧸ P) := ht.module
    let e := RingHom.quotientKerEquivOfSurjective hs
    letI : Module F (N ⧸ P) := Module.compHom (N ⧸ P) (e.symm : F →+* R ⧸ K)
    have hcomp : ∀ (b : R) (q : N ⧸ P), φ b • q = b • q := by
      intro b q
      show (e.symm (φ b)) • q = b • q
      rw [← RingHom.quotientKerEquivOfSurjective_apply_mk hs b, RingEquiv.symm_apply_apply]
      exact Module.IsTorsionBySet.mk_smul ht b q
    have hq : Submodule.Quotient.mk (p := P) y ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual F (N ⧸ P), f (Submodule.Quotient.mk y) ≠ 0 := by
      by_contra! h
      exact hq ((Module.forall_dual_apply_eq_zero_iff F _).1 h)
    let μ : N →+ F := f.toAddMonoidHom.comp P.mkQ.toAddMonoidHom
    have hμ : μ ∈ L := (hL μ).2 fun b z => by
      show f (Submodule.Quotient.mk (b • z)) = φ b * f (Submodule.Quotient.mk z)
      rw [Submodule.Quotient.mk_smul, ← hcomp, map_smul, smul_eq_mul]
    exact hf (hy μ hμ)
  refine ⟨hfin, hkill, ?_⟩
  intro ξ
  haveI := hfin
  let ev : N → Module.Dual F L := fun y =>
    { toFun := fun μ => (μ : N →+ F) y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W : Submodule F (Module.Dual F L) :=
    { carrier := {a | ∃ y : N, ∀ μ : L, (μ : N →+ F) y = a μ}
      add_mem' := by
        rintro a b ⟨y, hy⟩ ⟨z, hz⟩
        exact ⟨y + z, fun μ => by rw [map_add (f := _), hy, hz]; rfl⟩
      zero_mem' := ⟨0, fun μ => by simp⟩
      smul_mem' := by
        rintro c a ⟨y, hy⟩
        obtain ⟨b, rfl⟩ := hs c
        exact ⟨b • y, fun μ => by rw [(hL _).1 μ.2, hy]; rfl⟩ }
  by_contra hξ
  change ξ ∉ W at hξ
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hξ inferInstance
  set μ := (Module.evalEquiv F L).symm f with hμdef
  have hμ0 : μ = 0 := by
    refine Subtype.ext (AddMonoidHom.ext fun y => ?_)
    have hm : f (ev y) ∈ W.map f := Submodule.mem_map_of_mem ⟨y, fun _ => rfl⟩
    rw [hfW, Submodule.mem_bot] at hm
    have := Module.apply_evalEquiv_symm_apply F L (ev y) f
    rw [← hμdef, hm] at this
    exact this
  have hfe : f = Module.evalEquiv F L μ := ((Module.evalEquiv F L).apply_symm_apply f).symm
  rw [hfe, hμ0, map_zero] at hf
  exact hf rfl

theorem UpperTheory.V.Pa.laDual :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), Module.Finite S.F S.La ∧ (∀ y : S.U.N, (∀ μ ∈ S.La, μ y = 0) → y ∈ maximalIdeal S.Bh • (⊤ : Submodule S.Bh S.U.N)) ∧ ∀ ξ : Module.Dual S.F S.La, ∃ y : S.U.N, ∀ μ : S.La, (μ : S.U.N →+ S.F) y = ξ μ := by
  intro l _ S
  have hs : Function.Surjective S.rF := fun c => by
    obtain ⟨o, ho⟩ := S.oo_surj c
    exact ⟨_, ho⟩
  haveI := S.U.fin
  haveI hN : Module.Finite S.Bh S.U.N :=
    Module.Finite.of_surjective (Submodule.projectionOnto S.U.N 1 S.U.compl.symm)
      (Submodule.projectionOnto_surjective S.U.compl.symm)
  obtain ⟨h1, h2, h3⟩ := UpperTheory.V.Pa.dual_functionals_finite_separating_surjective S.rF hs S.La (fun μ => Iff.rfl)
  refine ⟨h1, fun y hy => ?_, h3⟩
  rw [← S.rF_ker]
  exact h2 y hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem conjugate_diagonal_zero_of_parity {R : Type} [CommRing R] {n : ℕ} (p q : Fin n → Bool)
    (w wi Z : Matrix (Fin n) (Fin n) R) (h1 : w * wi = 1) (h2 : wi * w = 1)
    (hw : ∀ i j, p i ≠ q j → w i j = 0) (hZ : ∀ i j, p i = p j → Z i j = 0) (i : Fin n) :
    (wi * Z * w) i i = 0 := by
  classical
  set P : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if p k then (1 : R) else 0) with hP
  set Q : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if q k then (1 : R) else 0) with hQ
  have hPw : P * w = w * Q := by
    ext a b
    rw [hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : p a = q b
    · rw [hab, mul_comm]
    · rw [hw a b hab]; simp
  have hQwi : Q * wi = wi * P := by
    calc Q * wi = (wi * w) * Q * wi := by rw [h2, Matrix.one_mul]
      _ = wi * (w * Q) * wi := by rw [Matrix.mul_assoc wi w Q]
      _ = wi * (P * w) * wi := by rw [hPw]
      _ = wi * P * (w * wi) := by simp only [Matrix.mul_assoc]
      _ = wi * P := by rw [h1, Matrix.mul_one]
  have hwi : ∀ a b, p b ≠ q a → wi a b = 0 := by
    intro a b hab
    have e := congrFun (congrFun hQwi a) b
    rw [hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    cases hpa : p b <;> cases hqa : q a <;> simp_all
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : p j = q i
  · by_cases hk : p k = q i
    · rw [hZ j k (hj.trans hk.symm)]; ring
    · rw [hw k i hk]; ring
  · rw [hwi i j hj]; ring

theorem UpperTheory.V.Pa.oddDiag :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (R : Type) [CommRing R] [Algebra x.A R] (v : L.Vl), x.wX R v * x.wiX R v = 1 ∧ x.wiX R v * x.wX R v = 1 ∧ (∀ Z ∈ Od x.A R n x.a, ∀ i, (x.wiX R v * Z * x.wX R v) i i = 0) ∧ (∀ g, (∀ i j, j < i → (x.wiX R v * x.ρX R (G0.φ v g) * x.wX R v) i j = 0) ∧ ∀ i, (x.wiX R v * x.ρX R (G0.φ v g) * x.wX R v) i i = algebraMap x.A R (x.ψ v i g)) ∧ (∀ g g', x.ρX R (g * g') = x.ρX R g * x.ρX R g') ∧ x.ρX R 1 = 1 ∧ (∀ g, x.ρX R g ∈ Ev x.A R n x.a) ∧ ∀ g, (x.ρX R g)ᵀ * x.ρX R (G0.frame.conj g) = algebraMap x.A R ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) R) := by
  intro l _ L G G0 h n x R _ _ v
  have hmat : ∀ g, mat x.ρ g = ((x.ρ g : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) := fun g => rfl
  have hconj : ∀ g, x.wiX R v * x.ρX R g * x.wX R v =
      ((((x.w v)⁻¹ * x.ρ g * x.w v : GL (Fin n) x.A)) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A R) := by
    intro g
    simp only [NP.wX, NP.wiX, NP.ρX, hmat, Units.val_mul, Matrix.map_mul]
  have hw1 : x.wX R v * x.wiX R v = 1 := by
    simp only [NP.wX, NP.wiX]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hw2 : x.wiX R v * x.wX R v = 1 := by
    simp only [NP.wX, NP.wiX]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨hw1, hw2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ i
    refine conjugate_diagonal_zero_of_parity (fun k => decide ((k : ℕ) < x.a)) (x.ty v) _ _ Z hw1 hw2 ?_ ?_ i
    · intro a b hab
      simp only [NP.wX, Matrix.map_apply]
      rw [x.w_blk v a b hab, map_zero]
    · intro a b hab
      have := (hZ a b).1 (by simpa using hab)
      simpa using this
  · intro g
    have t := x.tri v g
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hconj, Matrix.map_apply]
      exact (congrArg (algebraMap x.A R) (t.1 i j hij)).trans (map_zero _)
    · rw [hconj, Matrix.map_apply]
      exact congrArg (algebraMap x.A R) (t.2 i)
  · intro g g'
    simp only [NP.ρX, map_mul, Matrix.map_mul]
  · simp only [NP.ρX, map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · intro g i j
    have hb := x.blk g i j
    refine ⟨fun _ => Submodule.mem_top, fun hn => ?_⟩
    have h0 := hb.2 hn
    rw [Submodule.mem_bot] at h0 ⊢
    simp only [NP.ρX, Matrix.map_apply, h0, map_zero]
  · intro g
    have e := x.form g
    have e2 := congrArg (fun M => M.map (algebraMap x.A R)) e
    simp only [Units.val_one, Matrix.mul_one] at e2
    simp only [NP.ρX, ← Matrix.transpose_map, ← Matrix.map_mul]
    rw [e2]
    ext i j
    by_cases hij : i = j
    · simp [Matrix.one_apply, GFrame.eps, hij]
    · simp [Matrix.one_apply, GFrame.eps, hij]
end

