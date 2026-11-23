module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ShaToShT
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {O W : Type} [CommRing O] [AddCommGroup W] [Module O W]

private theorem shT_mono (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (F : ℕ) {a b : O} (h : a ∣ b) :
    ShT W α δ F a ≤ ShT W α δ F b := by
  obtain ⟨t, rfl⟩ := h
  rintro c ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, fun g => by rw [mul_comm, mul_smul, h3, smul_zero], h4, fun A hA => ?_⟩
  obtain ⟨m, hm, h⟩ := h5 A hA
  exact ⟨m, by rw [mul_comm, mul_smul, hm, smul_zero], h⟩

private theorem norm_coc (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (hδ : IsUnit ((α δ : O) - 1)) (c : G ℚ Ω → W)
    (hc : IsCoc α c) : ∃ m : W, IsCoc α (fun g => c g - ((α g : O) • m - m)) ∧ c δ - ((α δ : O) • m - m) = 0 := by
  set u := hδ.unit with hu0
  have hu : (u : O) = (α δ : O) - 1 := hδ.unit_spec
  refine ⟨((u⁻¹ : Oˣ) : O) • c δ, ⟨?_, fun g h => ?_⟩, ?_⟩
  · have hloc : IsLocallyConstant fun g : G ℚ Ω => c (g * δ) :=
      hc.1.comp_continuous (continuous_mul_const δ)
    have heq : (fun g => c g - ((α g : O) • ((u⁻¹ : Oˣ) : O) • c δ - ((u⁻¹ : Oˣ) : O) • c δ)) =
        fun g => c g - (((u⁻¹ : Oˣ) : O) • (c (g * δ) - c g) - ((u⁻¹ : Oˣ) : O) • c δ) := by
      funext g
      rw [hc.2 g δ, add_sub_cancel_left, smul_comm (α g : O)]
    rw [heq]
    exact hc.1.sub (((hloc.sub hc.1).comp fun v => ((u⁻¹ : Oˣ) : O) • v).sub
      (IsLocallyConstant.const _))
  · beta_reduce
    rw [hc.2 g h, map_mul, Units.val_mul, mul_smul]
    module
  · have e : (α δ : O) • (((u⁻¹ : Oˣ) : O) • c δ) - ((u⁻¹ : Oˣ) : O) • c δ =
        (u : O) • (((u⁻¹ : Oˣ) : O) • c δ) := by
      rw [hu, sub_smul, one_smul]
    rw [e, smul_smul, Units.mul_inv, one_smul, sub_self]

private theorem unit_kill {x : O} (hx : IsUnit x) {a : O} {w : W} (h : a • x • w = 0) : a • w = 0 := by
  obtain ⟨u, rfl⟩ := hx
  calc a • w = ((u⁻¹ : Oˣ) : O) • (a • (u : O) • w) := by
        rw [smul_comm _ a]
        simp [smul_smul]
    _ = 0 := by rw [h, smul_zero]

private theorem conj_cob (α : G ℚ Ω →* Oˣ) {c : G ℚ Ω → W} (hc : IsCoc α c) (σ x : G ℚ Ω) (m : W)
    (h : c (σ⁻¹ * x * σ) = (α (σ⁻¹ * x * σ) : O) • m - m) :
    c x = (α x : O) • ((α σ : O) • m - c σ) - ((α σ : O) • m - c σ) := by
  have hc1 : c 1 = 0 := by
    have := hc.2 1 1
    simp only [mul_one, map_one, Units.val_one, one_smul] at this
    exact left_eq_add.mp this
  have e0 : c σ⁻¹ + (α σ⁻¹ : O) • c σ = 0 := by
    rw [← hc.2, inv_mul_cancel, hc1]
  have e1 : c (σ⁻¹ * x * σ) = c σ⁻¹ + (α σ⁻¹ : O) • (c x + (α x : O) • c σ) := by
    rw [mul_assoc, hc.2, hc.2]
  have ea : (α (σ⁻¹ * x * σ) : O) = (α x : O) := by
    rw [map_mul, map_mul, map_inv]
    congr 1
    calc (α σ)⁻¹ * α x * α σ = α x * ((α σ)⁻¹ * α σ) := by ac_rfl
      _ = α x := by rw [inv_mul_cancel, mul_one]
  have hs : (α σ : O) * (α σ⁻¹ : O) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [e1, ea] at h
  linear_combination (norm := module) (α σ : O) • h - (α σ : O) • e0 - hs • (c x + (α x : O) • c σ - c σ)

private theorem dec_of_ine (α : G ℚ Ω →* Oˣ) {c : G ℚ Ω → W} (hc : IsCoc α c) (g d : G ℚ Ω) (m : W)
    (hg : IsUnit ((α g : O) - 1)) (h : c g = (α g : O) • m - m)
    (h' : c (d⁻¹ * g * d) = (α (d⁻¹ * g * d) : O) • m - m) : c d = (α d : O) • m - m := by
  have key := conj_cob α hc d g m h'
  rw [h] at key
  have e : ((α g : O) - 1) • m = ((α g : O) - 1) • ((α d : O) • m - c d) := by
    rw [sub_smul, one_smul, sub_smul, one_smul]
    exact key
  rw [hg.smul_left_cancel] at e
  linear_combination (norm := module) e

end

private theorem mem_shT (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (F : ℕ)
    (h1 : ∀ A : ValuationSubring Ω, ¬ Over A F → ∀ g ∈ Ine (F := ℚ) A, α g = 1)
    (h2 : ∀ A : ValuationSubring Ω, Over A F → ¬ Over A l → ∃ g ∈ Ine (F := ℚ) A, IsUnit ((α g : O) - 1))
    (c : G ℚ Ω → QO l O) (hc : IsCoc α c) (hδ : c δ = 0)
    (hs : ∀ D ∈ shaFam ℚ Ω l, ∃ m : QO l O, ∀ g ∈ D, c g = (α g : O) • m - m) :
    ∃ a : O, a ≠ 0 ∧ c ∈ ShT (QO l O) α δ F a := by
  classical
  obtain ⟨A0, hA0⟩ := (placeBasic Ω).1 l (Fact.out : l.Prime)
  obtain ⟨m0, hm0⟩ := hs (Dec A0) (Or.inl ⟨A0, hA0, rfl⟩)
  have hfin : (Set.range c).Finite := hc.1.range_finite
  choose ann hann0 hann using (UpperTheory.V.ML.qoCyc l O).1
  let S : Finset (QO l O) := insert m0 hfin.toFinset
  refine ⟨∏ w ∈ S, ann w, Finset.prod_ne_zero_iff.mpr fun w _ => hann0 w, ?_⟩
  have kill : ∀ w ∈ S, (∏ w ∈ S, ann w) • w = 0 :=
    fun w hw => (hann w _).mpr (Finset.dvd_prod_of_mem _ hw)
  set a := ∏ w ∈ S, ann w
  have killc : ∀ g, a • c g = 0 :=
    fun g => kill _ (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨g, rfl⟩))
  have killm0 : a • m0 = 0 := kill _ (Finset.mem_insert_self _ _)
  refine ⟨hc, hδ, killc, fun A hA g hg => ?_, fun A hA => ?_⟩
  · obtain ⟨m, hm⟩ := hs (Ine A) (Or.inr ⟨A, rfl⟩)
    rw [hm g hg, h1 A hA g hg, Units.val_one, one_smul, sub_self]
  · by_cases hl : Over A l
    · obtain ⟨σ, rfl⟩ := (placeBasic Ω).2.2.2.2.2.2.2.1 A0 A l (Fact.out : l.Prime) hA0 hl
      refine ⟨(α σ : O) • m0 - c σ, ?_, fun d hd => ?_⟩
      · rw [smul_sub, smul_comm a (α σ : O) m0, killm0, smul_zero, killc, sub_zero]
      · have hd' : σ⁻¹ * d * σ ∈ Dec A0 := (((placeBasic Ω).2.2.2.2.2.2.2.2.2 A0 σ).1 d).mp hd
        exact conj_cob α hc σ d m0 (hm0 _ hd')
    · obtain ⟨g0, hg0, hu⟩ := h2 A hA hl
      obtain ⟨m, hm⟩ := hs (Ine A) (Or.inr ⟨A, rfl⟩)
      refine ⟨m, ?_, fun d hd => ?_⟩
      · have e : ((α g0 : O) - 1) • m = c g0 := by rw [hm g0 hg0, sub_smul, one_smul]
        exact unit_kill hu (by rw [e, killc])
      · have hdA : d • A = A := mem_Dec.mp hd
        have hg' : d⁻¹ * g0 * d ∈ Ine A := by
          have hh := ((placeBasic Ω).2.2.2.2.2.2.2.2.2 A d).2.1 g0
          rw [hdA] at hh
          exact hh.mp hg0
        exact dec_of_ine α hc g0 d m hu (hm g0 hg0) (hm _ hg')

theorem UpperTheory.V.ML.shaToShT :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω), IsUnit ((α δ : O) - 1) → ∀ F : ℕ, F ≠ 0 →
    (∀ A : ValuationSubring Ω, ¬ Over A F → ∀ g ∈ Ine (F := ℚ) A, α g = 1) →
    (∀ A : ValuationSubring Ω, Over A F → ¬ Over A l → ∃ g ∈ Ine (F := ℚ) A, IsUnit ((α g : O) - 1)) → ∀ n : ℕ∞,
    (∀ a : O, a ≠ 0 → Module.length O (ShT (QO l O) α δ F a) ≤ n) → Module.length O (ShaU (twist₂ l α) l (⊤ : Subgroup (G ℚ Ω))) ≤ n := by
  intro Ω _ _ _ l _ O _ _ _ _ _ α δ hδ F hF h1 h2 n hn
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let T : Subgroup (G ℚ Ω) := ⊤
  let ι : Z1U (twist₂ l α) T →ₗ[O] (G ℚ Ω → QO l O) :=
    { toFun := fun z g => (z : T → QO l O) ⟨g, Subgroup.mem_top g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro z z' h
    apply Subtype.ext
    funext u
    exact congrFun h u.1
  let Q : Z1U (twist₂ l α) T →ₗ[O] H1U (twist₂ l α) T := Submodule.mkQ _
  let P : ℕ → Submodule O (H1U (twist₂ l α) T) := fun k =>
    ((ShT (QO l O) α δ F (ϖ ^ k)).comap ι).map Q
  refine UpperTheory.V.Kum.lenDirected O (H1U (twist₂ l α) T) (ShaU (twist₂ l α) l T) P n ?_ ?_ ?_
  · intro i j hij
    exact Submodule.map_mono (Submodule.comap_mono (shT_mono α δ F (pow_dvd_pow ϖ hij)))
  · intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hloc := UpperTheory.V.Base.mk_mem_locSel.mp hx
    obtain ⟨hzc, hzco⟩ := z.2
    set c : G ℚ Ω → QO l O := ι z with hcE
    have hcoc : IsCoc α c := by
      refine ⟨(IsLocallyConstant.iff_continuous _).mpr
        (hzc.comp (continuous_id.subtype_mk fun g => Subgroup.mem_top g)), fun g h => ?_⟩
      exact hzco ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩
    obtain ⟨m, hc', hδ'⟩ := norm_coc α δ hδ c hcoc
    set c' : G ℚ Ω → QO l O := fun g => c g - ((α g : O) • m - m) with hcE'
    have hs : ∀ D ∈ shaFam ℚ Ω l, ∃ m' : QO l O, ∀ g ∈ D, c' g = (α g : O) • m' - m' := by
      intro D hD
      obtain ⟨mD, hmD⟩ := hloc D hD
      refine ⟨mD - m, fun g hg => ?_⟩
      have e := hmD ⟨g, Subgroup.mem_top g⟩ hg
      change c g = (α g : O) • mD - mD at e
      simp only [hcE', e]
      module
    obtain ⟨a, ha0, hmem⟩ := mem_shT Ω l O α δ F h1 h2 c' hc' hδ' hs
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hmem' : c' ∈ ShT (QO l O) α δ F (ϖ ^ k) :=
      shT_mono α δ F (Units.mul_left_dvd.mpr dvd_rfl) hmem
    let z' : Z1U (twist₂ l α) T := ⟨fun v => c' v.1,
      (hc'.1.comp_continuous continuous_subtype_val).continuous, fun v w => hc'.2 v.1 w.1⟩
    have hq : Q z = Q z' := by
      simp only [Q, Submodule.mkQ_apply]
      rw [UpperTheory.V.Base.mk_eq_mk]
      refine ⟨m, fun v => ?_⟩
      change c v.1 - c' v.1 = (α v.1 : O) • m - m
      simp only [hcE']
      abel
    change Q z ∈ _
    rw [hq]
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_map_of_mem (show z' ∈ _ from hmem'))
  · intro n₀
    refine ⟨n₀, le_rfl, ?_⟩
    calc Module.length O (P n₀) ≤ Module.length O ((ShT (QO l O) α δ F (ϖ ^ n₀)).comap ι) :=
          Module.length_le_of_surjective (Q.submoduleMap _) (LinearMap.submoduleMap_surjective Q _)
      _ ≤ Module.length O (ShT (QO l O) α δ F (ϖ ^ n₀)) :=
          Module.length_le_of_injective (ι.restrict fun x hx => hx)
            (fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy)))
      _ ≤ n := hn _ (pow_ne_zero _ hϖ.ne_zero)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XCongPrin
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

namespace UpperTheory.V.ML.XCP

private def Rel {K' k : Type} [Field K'] [NumberField K'] [Field k] (π : 𝓞 K' →+* k) (a : K') (b : k) : Prop :=
  ∃ n d : 𝓞 K', π n ≠ 0 ∧ π d ≠ 0 ∧ a * algebraMap _ K' d = algebraMap _ K' n ∧ b * π d = π n

section
variable {K' k : Type} [Field K'] [NumberField K'] [Field k] {π : 𝓞 K' →+* k}

private theorem rel_int (x : 𝓞 K') (hx : π x ≠ 0) : Rel π (x : K') (π x) :=
  ⟨x, 1, hx, by simp, by simp, by simp⟩

private theorem rel_one : Rel π 1 1 := ⟨1, 1, by simp, by simp, by simp, by simp⟩

private theorem rel_mul {a a' : K'} {b b' : k} (h : Rel π a b) (h' : Rel π a' b') : Rel π (a * a') (b * b') := by
  obtain ⟨n, d, hn, hd, h1, h2⟩ := h
  obtain ⟨n', d', hn', hd', h1', h2'⟩ := h'
  refine ⟨n * n', d * d', by simp [hn, hn'], by simp [hd, hd'], ?_, ?_⟩
  · rw [map_mul, map_mul, ← h1, ← h1']; ring
  · rw [map_mul, map_mul, ← h2, ← h2']; ring

private theorem rel_inv {a : K'} {b : k} (h : Rel π a b) : Rel π a⁻¹ b⁻¹ := by
  obtain ⟨n, d, hn, hd, h1, h2⟩ := h
  have hn0 : algebraMap _ K' n ≠ 0 := by
    intro h
    have : n = 0 := by simpa using h
    exact hn (by simp [this])
  have ha : a ≠ 0 := by rintro rfl; exact hn0 (by simpa using h1.symm)
  have hb : b ≠ 0 := by rintro rfl; exact hn (by simpa using h2.symm)
  refine ⟨d, n, hd, hn, ?_, ?_⟩
  · rw [← h1]; field_simp
  · rw [← h2]; field_simp

private theorem rel_pow {a : K'} {b : k} (h : Rel π a b) (n : ℕ) : Rel π (a ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using rel_one
  | succ n ih => rw [pow_succ, pow_succ]; exact rel_mul ih h

private theorem rel_zpow {a : K'} {b : k} (h : Rel π a b) (n : ℤ) : Rel π (a ^ n) (b ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using rel_pow h m
  · simpa using rel_inv (rel_pow h m)

private theorem rel_prod {ι : Type} (s : Finset ι) {a : ι → K'} {b : ι → k} (h : ∀ i, Rel π (a i) (b i)) :
    Rel π (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_one
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi]; exact rel_mul (h i) ih

private theorem rel_val (v : HeightOneSpectrum (𝓞 K')) (hv : ∀ x, π x = 0 ↔ x ∈ v.asIdeal) {a a' : K'} {b : k}
    (h : Rel π a b) (h' : Rel π a' b) : v.valuation K' (a - a') < 1 := by
  obtain ⟨n, d, hn, hd, h1, h2⟩ := h
  obtain ⟨n', d', hn', hd', h1', h2'⟩ := h'
  have e : (a - a') * algebraMap _ K' (d * d') = algebraMap _ K' (n * d' - n' * d) := by
    rw [map_mul, map_sub, map_mul, map_mul, ← h1, ← h1']; ring
  have e1 : v.valuation K' (algebraMap _ K' (d * d')) = 1 := by
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem, ← hv]
    simp [hd, hd']
  have e2 : v.valuation K' (algebraMap _ K' (n * d' - n' * d)) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem, ← hv, map_sub, map_mul, map_mul, ← h2, ← h2']
    ring
  rwa [← e, map_mul, e1, mul_one] at e2

private theorem hom_ext {N q : ℕ} [NeZero N] [IsCyclotomicExtension {N} ℚ K'] (hq : q.Prime) [CharP k q]
    {ζ : K'} (hζ : IsPrimitiveRoot ζ N) (φ ψ : 𝓞 K' →+* k) (h : φ hζ.toInteger ^ q = ψ hζ.toInteger ^ q) :
    φ = ψ := by
  haveI := Fact.mk hq
  have h1 : φ hζ.toInteger = ψ hζ.toInteger := frobenius_inj k q h
  have h2 : φ.toIntAlgHom = ψ.toIntAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ) (by
      rintro _ rfl; exact h1)
  ext x
  exact DFunLike.congr_fun h2 x

end

private theorem compat (M N : ℕ) [NeZero M] [NeZero N] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] [Algebra K K']
    (h : M ∣ N) (t : (ZMod N)ˣ) (x : K) :
    sg N K' t (algebraMap K K' x) = algebraMap K K' (sg M K (ZMod.unitsMap h t) x) := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  have h1 := IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K' K h (sg N K' t)
  rw [sg, MulEquiv.apply_symm_apply] at h1
  rw [← h1, sg, sg, MulEquiv.symm_apply_apply, AlgEquiv.restrictNormal_commutes]

private theorem comb {G G' k : Type} [CommGroup G] [Fintype G] [DecidableEq G] [Fintype G'] [Field k] (p : G' → G) (u : G) (q : ℕ)
    (hq : 0 < q) (f : G → k) (hf : ∀ t, f t ≠ 0) (hfu : ∀ t, f t = f (u * t) ^ q) (a : G → ℤ) (a' : G' → ℤ)
    (ha : ∀ t, ∑ t' ∈ Finset.univ.filter (fun t' => p t' = t), a' t' = a t - a (u⁻¹ * t)) :
    ∏ t', f (p t') ^ a' t' = ∏ t, (f (u * t) ^ (q - 1)) ^ a t := by
  rw [← Finset.prod_fiberwise Finset.univ p]
  have h1 : ∀ t, ∏ t' ∈ Finset.univ.filter (fun t' => p t' = t), f (p t') ^ a' t'
      = f t ^ a t / f t ^ a (u⁻¹ * t) := by
    intro t
    rw [← zpow_sub₀ (hf t), ← ha, Finset.prod_congr rfl (g := fun t' => f t ^ a' t')
      (fun t' ht' => by rw [(Finset.mem_filter.1 ht').2])]
    induction (Finset.univ.filter (fun t' => p t' = t)) using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ (hf t)]
  rw [Finset.prod_congr rfl (fun t _ => h1 t), Finset.prod_div_distrib,
    ← Equiv.prod_comp (Equiv.mulLeft u) (fun t => f t ^ a (u⁻¹ * t)), ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
  rw [← div_zpow, hfu t]
  congr 1
  obtain ⟨q, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have := hf (u * t)
  rw [pow_succ, Nat.add_sub_cancel]
  field_simp

private theorem card_gal (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K']
    [IsGalois K K'] (hq : q.Prime) (hc : q.Coprime M) : Fintype.card Gal(K'/K) = q - 1 := by
  have h1 := Module.finrank_mul_finrank ℚ K K'
  rw [IsCyclotomicExtension.Rat.finrank M K, IsCyclotomicExtension.Rat.finrank (q * M) K', Nat.totient_mul hc,
    Nat.totient_prime hq, mul_comm] at h1
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.2 (NeZero.pos M)) h1

end UpperTheory.V.ML.XCP

open UpperTheory.V.ML.XCP in
theorem UpperTheory.V.ML.xCongPrin :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < q → ∀ y : 𝓞 K', (∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → y ∉ v.asIdeal) →
    ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal →
    v.valuation K' ((∏ t : (ZMod (q * M))ˣ, (sg (q * M) K' t)⁻¹ (y : K') ^ th (q * M) b t) -
      algebraMap K K' ((sg M K u)⁻¹ (∏ t : (ZMod M)ˣ, (sg M K t)⁻¹ (Algebra.norm K (y : K')) ^ th M b t))) < 1 := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hb y hy v hv
  classical
  haveI := Fact.mk hq
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  haveI := v.isMaximal
  letI : Field (𝓞 K' ⧸ v.asIdeal) := Ideal.Quotient.field _
  obtain ⟨π, hπ⟩ : ∃ π : 𝓞 K' →+* (𝓞 K' ⧸ v.asIdeal), ∀ x, π x = 0 ↔ x ∈ v.asIdeal :=
    ⟨Ideal.Quotient.mk _, fun x => Ideal.Quotient.eq_zero_iff_mem⟩
  haveI : CharP (𝓞 K' ⧸ v.asIdeal) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast π, hπ]; exact hv)
  have hc : q.Coprime M := by
    rw [← ZMod.isUnit_iff_coprime, ← hu]; exact u.isUnit
  have hd : M ∣ q * M := Dvd.intro_left q rfl

  let act : Gal(K'/ℚ) → 𝓞 K' →+* 𝓞 K' := fun σ => (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom
  have hact : ∀ σ x, ((act σ x : 𝓞 K') : K') = σ (x : K') := fun _ _ => rfl
  have hmul : ∀ σ τ x, act (σ * τ) x = act σ (act τ x) := fun _ _ _ => rfl
  have hne : ∀ σ, π (act σ y) ≠ 0 := by
    intro σ h
    have hq0 : (q : 𝓞 K') ∈ RingHom.ker (π.comp (act σ)) := by
      rw [RingHom.mem_ker, map_natCast]; exact CharP.cast_eq_zero _ q
    refine hy ⟨RingHom.ker (π.comp (act σ)), RingHom.ker_isPrime _, fun h0 => ?_⟩ hq0 h
    rw [h0, Ideal.mem_bot] at hq0
    exact hq.ne_zero (by exact_mod_cast hq0)
  have hζ := IsCyclotomicExtension.zeta_spec (q * M) ℚ K'
  set ζ := IsCyclotomicExtension.zeta (q * M) ℚ K'
  obtain ⟨w, hw, hwζ⟩ : ∃ w : K, w ^ M = 1 ∧ algebraMap K K' w = ζ ^ q := by
    have h0 := IsCyclotomicExtension.zeta_spec M ℚ K
    have h1 := h0.map_of_injective (algebraMap K K').injective
    obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one (ξ := ζ ^ q) (by rw [← pow_mul, hζ.pow_eq_one])
    exact ⟨_ ^ i, by rw [pow_right_comm, h0.pow_eq_one, one_pow], by rw [map_pow, hi]⟩
  have hcoe : ((hζ.toInteger : 𝓞 K') : K') = ζ := rfl
  have hA : ∀ σ τ : Gal(K'/ℚ), σ (algebraMap K K' w) = τ (algebraMap K K' w) → ∀ x, π (act σ x) = π (act τ x) := by
    intro σ τ h x
    have : π.comp (act σ) = π.comp (act τ) := by
      refine hom_ext hq hζ _ _ ?_
      rw [← map_pow, ← map_pow, RingHom.comp_apply, RingHom.comp_apply]
      congr 1
      apply RingOfIntegers.ext
      rw [hact, hact]
      rw [hwζ] at h
      exact h
    exact DFunLike.congr_fun this x
  choose s hs using ZMod.unitsMap_surjective hd
  have hB : ∀ x, π (act (sg (q * M) K' (s u)) x) = π x ^ q := by
    intro x
    have : π.comp (act (sg (q * M) K' (s u))) = (frobenius _ q).comp π := by
      refine hom_ext hq hζ _ _ ?_
      rw [← map_pow, ← map_pow, RingHom.comp_apply, RingHom.comp_apply, frobenius_def, ← map_pow π]
      congr 1
      apply RingOfIntegers.ext
      rw [hact]
      change sg (q * M) K' (s u) (ζ ^ q) = (ζ ^ q) ^ q
      rw [← hwζ, compat M (q * M) K K' hd, hs, sg_apply M K u hw, ← map_pow, hu, ZMod.val_natCast,
        ← pow_eq_pow_mod _ hw]
    exact DFunLike.congr_fun this x
  let f : (ZMod M)ˣ → 𝓞 K' ⧸ v.asIdeal := fun t => π (act (sg (q * M) K' (s t)⁻¹) y)
  have hf : ∀ t' : (ZMod (q * M))ˣ, π (act (sg (q * M) K' t'⁻¹) y) = f (ZMod.unitsMap hd t') := by
    intro t'
    refine hA _ _ ?_ y
    rw [compat M (q * M) K K' hd, compat M (q * M) K K' hd, map_inv (ZMod.unitsMap hd), map_inv (ZMod.unitsMap hd), hs]
  have hfu : ∀ t, f t = f (u * t) ^ q := by
    intro t
    have h1 := hf ((s u)⁻¹ * s (u * t))
    rw [map_mul (ZMod.unitsMap hd), map_inv (ZMod.unitsMap hd), hs, hs, inv_mul_cancel_left, mul_inv, inv_inv, map_mul, hmul, hB] at h1
    exact h1.symm
  have hcomb := comb (ZMod.unitsMap hd) u q hq.pos f (fun t => hne _) hfu (fun t => th M b t)
    (fun t => th (q * M) b t) (fun t => by convert thDist M q b hq hb u hu t)
  refine rel_val v hπ (b := ∏ t' : (ZMod (q * M))ˣ, f (ZMod.unitsMap hd t') ^ th (q * M) b t') ?_ ?_
  · refine rel_prod _ fun t => rel_zpow ?_ _
    rw [← hf, ← map_inv, ← hact]
    exact rel_int _ (hne _)
  · rw [hcomb, map_prod, map_prod]
    refine rel_prod _ fun t => ?_
    rw [map_zpow₀, map_zpow₀]
    refine rel_zpow ?_ _
    have h1 : (sg M K u)⁻¹ ((sg M K t)⁻¹ (Algebra.norm K (y : K')))
        = sg M K (ZMod.unitsMap hd (s (u * t))⁻¹) (Algebra.norm K (y : K')) := by
      rw [map_inv (ZMod.unitsMap hd), hs, mul_inv, map_mul, map_inv, map_inv]; rfl
    rw [h1, ← compat M (q * M) K K' hd, Algebra.norm_eq_prod_automorphisms, map_prod,
      ← card_gal M q K K' hq hc, ← Finset.card_univ, ← Finset.prod_const]
    refine rel_prod _ fun σ => ?_
    have h2 : f (u * t) = π (act (sg (q * M) K' (s (u * t))⁻¹ * σ.restrictScalars ℚ) y) := by
      refine hA _ _ ?_ y
      rw [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
    rw [h2]
    exact rel_int (act (sg (q * M) K' (s (u * t))⁻¹ * σ.restrictScalars ℚ) y) (hne _)
end

