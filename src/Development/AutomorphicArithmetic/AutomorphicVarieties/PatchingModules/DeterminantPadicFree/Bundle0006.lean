module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ResSqField
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.Det.resSq_fin {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [Module.Finite K K'] : (PowerSeries.map (algebraMap K K')).Finite := by
  classical
  letI := (PowerSeries.map (algebraMap K K')).toAlgebra
  let b := Module.finBasis K K'
  show Module.Finite (PowerSeries K) (PowerSeries K')
  refine ⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩
  rw [eq_top_iff]
  intro φ _
  have key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) •
      PowerSeries.C (b i) := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_map, PowerSeries.coeff_mk]
    simp_rw [← Algebra.smul_def]
    exact (b.sum_repr _).symm
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

private theorem UpperTheory.V.Pa.Det.resSq_field (K : Type) [Field K] [Finite K] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K'),
      ∀ a : K, IsSquare (algebraMap K K' a) := by
  classical
  letI := Fintype.ofFinite K
  let p : Polynomial K := ∏ a : K, (Polynomial.X ^ 2 - Polynomial.C a)
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ =>
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) a
  refine ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, fun a => ?_⟩
  have hs := Polynomial.SplittingField.splits p
  have hd : (Polynomial.X ^ 2 - Polynomial.C a) ∣ p := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
  have hs' : ((Polynomial.X ^ 2 - Polynomial.C a).map (algebraMap K p.SplittingField)).Splits :=
    hs.of_dvd (Polynomial.map_ne_zero hp) (Polynomial.map_dvd _ hd)
  obtain ⟨x, hx⟩ := hs'.exists_eval_eq_zero (by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
  refine ⟨x, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx
  rw [← sq]; exact (sub_eq_zero.mp hx).symm

theorem UpperTheory.V.Pa.Det.resSq :
    ∀ {K : Type} [Field K] [Finite K], ∃ (K' : Type) (_ : Field K') (_ : Finite K') (j : PowerSeries K →+* PowerSeries K'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ ∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j c)) := by
  intro K _ _
  obtain ⟨K', _, _, _, hsq⟩ := UpperTheory.V.Pa.Det.resSq_field K
  haveI : Finite K' := Module.finite_of_finite K
  have hcc : ∀ φ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map (algebraMap K K') φ) =
      algebraMap K K' (PowerSeries.constantCoeff φ) := by
    intro φ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine ⟨K', inferInstance, inferInstance, PowerSeries.map (algebraMap K K'),
    PowerSeries.map_injective _ (algebraMap K K').injective, ⟨fun φ hφ => ?_⟩,
    UpperTheory.V.Pa.Det.resSq_fin, fun c => ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero,
      map_ne_zero_iff _ (algebraMap K K').injective] at hφ
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hφ
  · obtain ⟨r, hr⟩ := hsq (PowerSeries.constantCoeff (c : PowerSeries K))
    refine ⟨residue (PowerSeries K') (PowerSeries.C r), ?_⟩
    rw [← map_mul, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, hcc, hr, map_mul,
      PowerSeries.constantCoeff_C, sub_self]
    exact not_isUnit_zero
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SelSub
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R]

private theorem dY_add (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (Y Y' : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (Y + Y') g = dY F ρ Y g + dY F ρ Y' g := by
  simp only [dY, Matrix.mul_add, Matrix.add_mul]
  abel

private theorem dY_zero (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (g : F.G₀) : dY F ρ 0 g = 0 := by
  simp [dY]

private theorem dY_smul (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (c : A) (Y : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (c • Y) g = c • dY F ρ Y g := by
  simp only [dY, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

private theorem ac_add {Γ : Type} [TopologicalSpace Γ] {I : Ideal R} {f f' : Γ → R} (h : AdicCont I f)
    (h' : AdicCont I f') : AdicCont I fun g => f g + f' g := by
  intro N
  have key := (h N).add (h' N)
  convert key using 1
  funext g
  simp [map_add (f := _)]

private theorem ac_smul {Γ : Type} [TopologicalSpace Γ] {I : Ideal R} {f : Γ → R} (c : A) (h : AdicCont I f) :
    AdicCont I fun g => c • f g := by
  intro N
  have key := (h N).comp (fun x => Ideal.Quotient.mk (I ^ N) (algebraMap A R c) * x)
  convert key using 1
  funext g
  simp [Function.comp, Algebra.smul_def, map_mul]

end

theorem UpperTheory.V.Pa.Det.selSub :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), (∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = SelZ F t ρ w wi V) ∧ ∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = Bd F ρ V := by
  intro l _ F n A R _ _ _ t ρ w wi V
  refine ⟨⟨⟨⟨⟨SelZ F t ρ w wi V, ?_⟩, ?_⟩, ?_⟩, rfl⟩, ⟨⟨⟨⟨Bd F ρ V, ?_⟩, ?_⟩, ?_⟩, rfl⟩⟩
  · intro z z' hz hz'
    simp only [SelZ, Set.mem_setOf_eq] at hz hz' ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
    obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := hz'
    refine ⟨fun g => V.add_mem (h1 g) (h1' g), fun i j => ?_, fun g k => ?_, fun g => ?_,
      fun u g hg => ?_, fun v => ?_⟩
    · have e := ac_add (h2 i j) (h2' i j)
      simpa only [Pi.add_apply, Matrix.add_apply] using e
    · rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, h3, h3', Matrix.mul_add, Matrix.add_mul]
      abel
    · rw [Pi.add_apply, Pi.add_apply, h4, h4', Matrix.transpose_add, neg_add]
    · rw [Pi.add_apply, h5 u g hg, h5' u g hg, add_zero]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      obtain ⟨Y', hY', hl'⟩ := h6' v
      refine ⟨Y + Y', V.add_mem hY hY', ?_⟩
      intro g
      obtain ⟨a, b⟩ := hl g
      obtain ⟨a', b'⟩ := hl' g
      have e : ∀ x, (z + z') x - dY F ρ (Y + Y') x = (z x - dY F ρ Y x) + (z' x - dY F ρ Y' x) := by
        intro x
        rw [Pi.add_apply, dY_add]
        abel
      refine ⟨fun i j hij => ?_, fun hm i => ?_⟩
      · rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, a i j hij, a' i j hij, add_zero]
      · rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, b hm i, b' hm i, add_zero]
  · simp only [SelZ, Set.mem_setOf_eq]
    refine ⟨fun g => V.zero_mem, fun i j => ?_, fun g k => ?_, fun g => ?_, fun u g hg => rfl, fun v => ?_⟩
    · intro N
      simp only [Pi.zero_apply, Matrix.zero_apply, map_zero]
      exact IsLocallyConstant.const 0
    · simp
    · simp
    · refine ⟨0, V.zero_mem, ?_⟩
      intro g
      simp [dY_zero]
  · intro c z hz
    simp only [SelZ, Set.mem_setOf_eq] at hz ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
    refine ⟨fun g => V.smul_mem c (h1 g), fun i j => ?_, fun g k => ?_, fun g => ?_,
      fun u g hg => ?_, fun v => ?_⟩
    · have e := ac_smul c (h2 i j)
      simpa only [Pi.smul_apply, Matrix.smul_apply] using e
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, h3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
    · rw [Pi.smul_apply, Pi.smul_apply, h4, Matrix.transpose_smul, smul_neg]
    · rw [Pi.smul_apply, h5 u g hg, smul_zero]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      refine ⟨c • Y, V.smul_mem c hY, ?_⟩
      intro g
      obtain ⟨a, b⟩ := hl g
      have e : ∀ x, (c • z) x - dY F ρ (c • Y) x = c • (z x - dY F ρ Y x) := by
        intro x
        rw [Pi.smul_apply, dY_smul, smul_sub]
      refine ⟨fun i j hij => ?_, fun hm i => ?_⟩
      · rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, a i j hij, smul_zero]
      · rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, b hm i, smul_zero]
  · rintro z z' ⟨Y, hY, hT, rfl⟩ ⟨Y', hY', hT', rfl⟩
    refine ⟨Y + Y', V.add_mem hY hY', by rw [Matrix.transpose_add, hT, hT', neg_add], ?_⟩
    funext g
    rw [Pi.add_apply, dY_add]
  · exact ⟨0, V.zero_mem, by simp, by funext g; rw [dY_zero]; rfl⟩
  · rintro c z ⟨Y, hY, hT, rfl⟩
    refine ⟨c • Y, V.smul_mem c hY, by rw [Matrix.transpose_smul, hT, smul_neg], ?_⟩
    funext g
    rw [Pi.smul_apply, dY_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SpanDesc
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem sd_map_ev {F F' : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ}
    {Z : Matrix (Fin n) (Fin n) F} (hZ : Z ∈ Ev F F n a) : Z.map f ∈ Ev F' F' n a := by
  intro i j
  refine ⟨fun _ => trivial, fun e => ?_⟩
  have h0 : Z i j = 0 := (hZ i j).2 e
  rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]

private theorem sd_up {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F)
    (hY : Y ∈ Submodule.span F (Set.range r)) :
    Y.map f ∈ Submodule.span F' (Set.range fun i => (r i).map f) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
    have : (0 : Matrix (Fin n) (Fin n) F).map f = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (y + z).map f = y.map f + z.map f := by ext i j; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (c • y).map f = f c • y.map f := by ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hy

private theorem sd_down {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (p : F' →+ F) (hp : ∀ (c : F') (x : F), p (c * f x) = p c * x)
    (Y : Matrix (Fin n) (Fin n) F')
    (hY : Y ∈ Submodule.span F' (Set.range fun i => (r i).map f)) :
    ∀ c : F', (c • Y).map p ∈ Submodule.span F (Set.range r) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    intro c
    have : (c • (r i).map f).map p = p c • r i := by
      ext s t; simp [hp]
    show (c • (r i).map f).map p ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero =>
    intro c
    have : (c • (0 : Matrix (Fin n) (Fin n) F')).map p = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    intro c
    have : (c • (y + z)).map p = (c • y).map p + (c • z).map p := by ext i j; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ (hy c) (hz c)
  | smul d y _ hy =>
    intro c
    rw [smul_smul]; exact hy _

theorem UpperTheory.V.Pa.Det.spanDesc :
    ∀ {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) F), (∀ i, r i ∈ Ev F F n a) → (Submodule.span F (Set.range r) = Ev F F n a ↔ Submodule.span F' (Set.range fun i => (r i).map f) = Ev F' F' n a) := by
  intro F F' ι _ _ f n a r hr
  constructor
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact sd_map_ev f (hr i)
    · intro Z hZ
      have hZ' : Z = ∑ i, ∑ j, single i j (Z i j) := matrix_eq_sum_single Z
      rw [hZ']
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
      · have h1 : (single i j 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a :=
          fun p q => ⟨fun _ => trivial, fun e' => by
            rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
            rintro ⟨rfl, rfl⟩
            exact e' e⟩
        rw [← h] at h1
        have h2 := Submodule.smul_mem _ (Z i j) (sd_up f r _ h1)
        convert h2 using 1
        ext p q
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
        split_ifs <;> simp
      · have : Z i j = 0 := (hZ i j).2 e
        simp [this]
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hr i
    · intro Z hZ
      letI : Algebra F F' := f.toAlgebra
      obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F F')
        (LinearMap.ker_eq_bot.2 f.injective)
      have hp1 : ∀ x : F, p (f x) = x := fun x => LinearMap.congr_fun hp x
      have hp2 : ∀ (c : F') (x : F), p.toAddMonoidHom (c * f x) = p.toAddMonoidHom c * x := by
        intro c x
        have h3 : c * f x = x • c := by rw [mul_comm]; rfl
        show p (c * f x) = p c * x
        rw [h3, map_smul, smul_eq_mul, mul_comm]
      have h1 := sd_map_ev f hZ
      rw [← h] at h1
      have h2 := sd_down f r p.toAddMonoidHom hp2 _ h1 1
      convert h2 using 1
      ext s t
      simp [hp1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SplitEx
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_injective_roots_in_integral_closure {A L : Type} [CommRing A] [Field L] [Algebra A L] {n : ℕ} (p : Polynomial A)
    (hm : p.Monic) (hn : (p.map (algebraMap A L)).natDegree = n) (hsep : (p.map (algebraMap A L)).Separable)
    (hs : (p.map (algebraMap A L)).Splits) :
    ∃ al : Fin n → integralClosure A L, Function.Injective al ∧
      p.map (algebraMap A (integralClosure A L)) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
  classical
  set pL := p.map (algebraMap A L) with hpL
  have hmL : pL.Monic := hm.map _
  have hroots : pL = (pL.roots.map fun x => Polynomial.X - Polynomial.C x).prod :=
    hs.eq_prod_roots_of_monic hmL
  have hnd : pL.roots.Nodup := Polynomial.nodup_roots hsep
  set s := pL.roots.toFinset with hsdef
  have hcard : s.card = n := by
    rw [hsdef, Multiset.toFinset_card_of_nodup hnd, ← hs.natDegree_eq_card_roots, hn]
  have hint : ∀ x ∈ s, x ∈ integralClosure A L := by
    intro x hx
    rw [hsdef, Multiset.mem_toFinset, Polynomial.mem_roots hmL.ne_zero, Polynomial.IsRoot,
      hpL, Polynomial.eval_map] at hx
    exact ⟨p, hm, hx⟩
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hcard)).symm
  refine ⟨fun b => ⟨(e b : L), hint _ (e b).2⟩, ?_, ?_⟩
  · intro b b' h
    have h2 := congrArg Subtype.val h
    exact e.injective (Subtype.ext h2)
  · apply Polynomial.map_injective (integralClosure A L).val.toRingHom Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_prod]
    have h1 : ((integralClosure A L).val.toRingHom).comp (algebraMap A (integralClosure A L)) =
        algebraMap A L := by
      ext a
      rfl
    rw [h1]
    change pL = _
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hroots]
    have h3 : ∏ b : Fin n, (Polynomial.X - Polynomial.C ((e b : L))) =
        ∏ x ∈ s, (Polynomial.X - Polynomial.C x) := by
      rw [Equiv.prod_comp e (fun x : s => Polynomial.X - Polynomial.C (x : L))]
      exact Finset.prod_coe_sort s (fun x => Polynomial.X - Polynomial.C x)
    convert h3.symm using 1
    · rw [Finset.prod_eq_multiset_prod, hsdef, Multiset.toFinset_val, hnd.dedup]
    · rfl

theorem UpperTheory.V.Pa.Det.splitEx :
    ∀ (l : ℕ) [Fact l.Prime] {K : Type} [Field K] [Finite K] [CharP K l] {q n : ℕ} (P : Fin q → Polynomial (PowerSeries K)), (∀ a, (P a).Monic ∧ (P a).natDegree = n ∧ ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).Separable) → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : IsEqDVR l A') (j : PowerSeries K →+* A') (al : Fin q → Fin n → A'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ ∀ a, Function.Injective (al a) ∧ (P a).map j = ∏ b, (Polynomial.X - Polynomial.C (al a b)) := by
  intro l _ K _ _ _ q n P hP
  classical
  have hQ0 : (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => ((hP a).1.map _).ne_zero
  haveI hsepE : Algebra.IsSeparable (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) := by
    rw [← IntermediateField.isSeparable_top,
      ← (isSplittingField_iff_intermediateField.mp
        (inferInstance : Polynomial.IsSplittingField (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).2,
      IntermediateField.isSeparable_adjoin_iff_isSeparable]
    intro x hx
    have h0 := Polynomial.aeval_eq_zero_of_mem_rootSet hx
    rw [map_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨a, _, ha⟩ := h0
    exact (hP a).2.2.of_dvd (minpoly.dvd (FractionRing (PowerSeries K)) x ha)
  haveI hcA : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hfinA : Finite (IsLocalRing.ResidueField (PowerSeries K)) :=
    Finite.of_equiv K (PowerSeries.residueFieldOfPowerSeries).symm.toEquiv
  set_option synthInstance.maxHeartbeats 400000 in
  obtain ⟨hfin, _, _, hdvr, hcB, hloc, hres⟩ :=
    UpperTheory.V.AlgebraTools.integralClosure_complete_dvr (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))
  have hinjAE : Function.Injective (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
    rw [IsScalarTower.algebraMap_eq (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))]
    exact (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).injective.comp (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hj : Function.Injective (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) := by
    intro x y h
    apply hinjAE
    exact congrArg Subtype.val h
  haveI hcharA : CharP (PowerSeries K) l := charP_of_injective_ringHom (PowerSeries.C (R := K)).injective l
  haveI hcharB : CharP ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) l := charP_of_injective_ringHom hj l
  have hal : ∀ a, ∃ al : Fin n → ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), Function.Injective al ∧
      (P a).map (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
    intro a
    have hdeg : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).natDegree = n := by
      rw [(hP a).1.natDegree_map]
      exact (hP a).2.1
    have hmapE : (P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) =
        ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).map (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hsepa : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Separable := by
      rw [hmapE]
      exact (hP a).2.2.map
    have hspl : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Splits := by
      rw [hmapE]
      refine Polynomial.Splits.of_dvd (Polynomial.SplittingField.splits (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))
        (Polynomial.map_ne_zero hQ0) ?_
      exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ a))
    exact exists_injective_roots_in_integral_closure (P a) (hP a).1 hdeg hsepa hspl
  choose al hal1 hal2 using hal
  exact ⟨↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), inferInstance, inferInstance, hdvr, ⟨hcB, hres hfinA, hcharB⟩, algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), al,
    hj, hloc, RingHom.finite_algebraMap.mpr hfin, fun a => ⟨hal1 a, hal2 a⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.TypeIDisc
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

open UpperTheory.V.CA in
private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one, h] at h1
  have h2 := (d_toDet (GDet.ofRep ρ) (MonoidAlgebra.single g 1)).2.2.1
  rw [d_toDet_ofRep.1, (d_ofRep _ _ _).2.2.1 hn] at h2
  have h3 : GDet.repAlg ρ K (MonoidAlgebra.single g 1) = ρ g := by
    ext i j; simp [GDet.repAlg]
  rw [h3] at h2
  exact h1.symm.trans h2.symm

private theorem span_top {n : ℕ} {A L : Type} [CommRing A] [Field L] [Algebra A L] (t : A)
    (ht : algebraMap A L t ≠ 0) (S : Set (Matrix (Fin n) (Fin n) A))
    (hS : ∀ Z, ∃ s : ℕ, t ^ s • Z ∈ Submodule.span A S) :
    Submodule.span L ((algebraMap A L).mapMatrix '' S) = ⊤ := by
  have h1 : ∀ Z ∈ Submodule.span A S, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      have : (algebraMap A L).mapMatrix (y + z) =
          (algebraMap A L).mapMatrix y + (algebraMap A L).mapMatrix z := by
        ext i j; simp
      rw [this]; exact add_mem hy hz
    | smul c y _ hy =>
      have : (algebraMap A L).mapMatrix (c • y) = algebraMap A L c • (algebraMap A L).mapMatrix y := by
        ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ hy
  have h2 : ∀ Z : Matrix (Fin n) (Fin n) A, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z
    obtain ⟨s, hs⟩ := hS Z
    have h := h1 _ hs
    have e : (algebraMap A L).mapMatrix (t ^ s • Z) = algebraMap A L t ^ s • (algebraMap A L).mapMatrix Z := by
      ext i j; simp
    rw [e] at h
    exact (Submodule.smul_mem_iff _ (pow_ne_zero s ht)).1 h
  rw [eq_top_iff]
  intro Z _
  rw [Matrix.matrix_eq_sum_single Z]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (Z i j) = Z i j • (algebraMap A L).mapMatrix (Matrix.single i j (1 : A)) := by
    ext a b
    by_cases h : i = a ∧ j = b <;> simp [Matrix.single_apply, h]
  rw [e]
  exact Submodule.smul_mem _ _ (h2 _)

theorem UpperTheory.V.Pa.Det.typeIDisc :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) {R : Type} [CommRing R] (D : GDet n R F.G₀) (f : R →+* x.A), x.a = n → D.map f = GDet.ofRep (mat x.ρ) → ∀ q : Ideal R, q ≤ RingHom.ker f → DiscSt D q := by
  intro l _ F n x R _ D f ha hD q hq
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  have ht : algebraMap x.A (FractionRing x.A) x.t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective x.A (FractionRing x.A))).2 PowerSeries.X_ne_zero
  have hsp := span_top (L := FractionRing x.A) x.t ht (mat x.ρ '' (F.G' : Set F.G₀)) fun Z =>
    x.span Z fun i j => ⟨fun _ => Submodule.mem_top, fun h => (h (by simp [ha])).elim⟩
  obtain ⟨y, hy, hdet⟩ := (UpperTheory.V.CA.g_gram _ _ _).1 hsp
  have hy' : ∀ a, ∃ g, (algebraMap x.A (FractionRing x.A)).mapMatrix (mat x.ρ g) = y a := fun a => by
    obtain ⟨_, ⟨g, -, rfl⟩, h⟩ := hy a
    exact ⟨g, h⟩
  choose g hg using hy'
  refine ⟨fun i => g (finProdFinEquiv.symm i), fun i => g (finProdFinEquiv.symm i), fun hm => hdet ?_⟩
  have h0 := congrArg (algebraMap x.A (FractionRing x.A)) (RingHom.mem_ker.1 (hq hm))
  rw [map_zero, ← RingHom.comp_apply, RingHom.map_det] at h0
  rw [← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm, ← h0]
  congr 1
  ext a b
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, tr_of_map hn D f _ hD,
    Matrix.submatrix_apply, Matrix.of_apply, ← hg, ← hg, ← map_mul, ← map_mul, RingHom.mapMatrix_apply]
  exact (AddMonoidHom.map_trace (algebraMap x.A (FractionRing x.A)) _).symm
end

