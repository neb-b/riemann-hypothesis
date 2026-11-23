module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormRingALe
section
noncomputable def UpperTheory.Reformulated.B.Qi27.muPrime :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Set ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ {ζ : ℂ_[l] | ∃ (n : ℕ), (0 : ℕ) < n ∧ ¬l ∣ n ∧ ζ ^ n = (1 : ℂ_[l])}

noncomputable def UpperTheory.Reformulated.B.Qi27.ringA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Subring ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Subring.closure (UpperTheory.Reformulated.B.Qi27.muPrime l)

theorem UpperTheory.Reformulated.B.Qi27.norm_ringA_le :
    ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {x : ℂ_[l]}, x ∈ UpperTheory.Reformulated.B.Qi27.ringA l → ‖x‖ ≤ (1 : ℝ) := by
  intro l hl x hx
  unfold UpperTheory.Reformulated.B.Qi27.ringA at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨n, hn, -, h⟩ := hy
    have h1 : ‖y‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg y) hn.ne').1 h1).le
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  | neg a _ ha => simpa using ha
  | mul a b _ _ ha hb =>
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan
section
namespace UpperTheory.Reformulated.B.NormalizedMatrixSpan

@[reducible] noncomputable def Mat (C : Type) (N : ℕ) : Type := Matrix (Fin N) (Fin N) C

noncomputable def Normd {C : Type} [Field C] {N : ℕ} {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C)
    (A : Subalgebra C (Mat C N)) : Prop :=
  ∀ g : Γ, ∀ a ∈ A,
    (ρ g : Matrix (Fin N) (Fin N) C) * a * (ρ g⁻¹ : Matrix (Fin N) (Fin N) C) ∈ A

noncomputable def gens {Γ C : Type} [Group Γ] [Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C)
    (A : Subalgebra C (Mat C N)) : Set (Mat C N) :=
  {x : Mat C N | ∃ a ∈ A, ∃ g : Γ, x = a * (ρ g : Matrix (Fin N) (Fin N) C)}

theorem span_mul {Γ C : Type} [Group Γ] [Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C)
    (A : Subalgebra C (Mat C N)) (hA : Normd ρ A) (x y : Mat C N)
    (hx : x ∈ Submodule.span C (gens ρ A)) (hy : y ∈ Submodule.span C (gens ρ A)) :
    x * y ∈ Submodule.span C (gens ρ A) := by
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, g, rfl⟩, _, ⟨b, hb, k, rfl⟩, rfl⟩
  refine ⟨a * ((ρ g : Matrix (Fin N) (Fin N) C) * b * (ρ g⁻¹ : Matrix (Fin N) (Fin N) C)),
    A.mul_mem ha (hA g b hb), g * k, ?_⟩
  have e : (ρ g⁻¹ : Matrix (Fin N) (Fin N) C) * (ρ (g * k) : Matrix (Fin N) (Fin N) C)
      = (ρ k : Matrix (Fin N) (Fin N) C) := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel_left]
  simp only [mul_assoc, e]

end UpperTheory.Reformulated.B.NormalizedMatrixSpan
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OddSpanVariable
section
theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X :
    ∀ {O σ ι : Type} [inst : CommRing O] (e : ι → σ) (s : Finset ι)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ),
        (∀ i ∈ s, (n : σ → ℕ) (e i) = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range fun (i : ι) ↦ MvPowerSeries.X (e i)) := by
  intro O σ ι inst e s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a s _ ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n (e a) = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g
        = if n (e a) = 0 then MvPowerSeries.coeff n f else 0 := fun _ => rfl
    have h1 : g ∈ Ideal.span (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) := by
      refine ih g fun n hn => ?_
      rw [hg]
      split_ifs with h
      · refine hf n fun i hi => ?_
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X (e a) : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have h3 : f - g ∈ Ideal.span
        (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OmMul
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe48.DR :
    (R B : Type) → [inst : CommRing R] → [inst_1 : CommRing B] → [Algebra R B] → Type :=
    fun (R B : Type) [CommRing R] [CommRing B] [Algebra R B] ↦ ExteriorAlgebra B Ω[B⁄R]

noncomputable def UpperTheory.Reformulated.B.Qe48.omB :
    (k : Type) →
      [inst : Field k] →
        (K : Type) →
          [inst_1 : Field K] → [inst_2 : Algebra k K] → Subalgebra k K → ℕ → Submodule k (UpperTheory.Reformulated.B.Qe48.DR k K) :=
    fun (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ) ↦
      Submodule.span k
        {y : UpperTheory.Reformulated.B.Qe48.DR k K |
          ∃ b ∈ B,
            ∃ (v : Fin q → K),
              (∀ (j : Fin q), v j ∈ B) ∧
                y =
                  b •
                    (ExteriorAlgebra.ιMulti K q : (Fin q → Ω[K⁄k]) → ExteriorAlgebra K Ω[K⁄k]) fun (j : Fin q) ↦
                      (KaehlerDifferential.D k K : K → Ω[K⁄k]) (v j)}

theorem UpperTheory.Reformulated.B.Qe48.om_mul :
    ∀ {L : Type} [inst : Field L] [inst_1 : Algebra ℂ L] (B : Subalgebra ℂ L) {p q : ℕ} {u w : UpperTheory.Reformulated.B.Qe48.DR ℂ L},
      u ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B p → w ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B q → u * w ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B (p + q) := by
  intro L _ _ B p q u w hu hw
  unfold UpperTheory.Reformulated.B.Qe48.omB at hu hw ⊢
  have h := Submodule.mul_mem_mul hu hw
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨b, hb, v, hv, rfl⟩, _, ⟨c, hc, v', hv', rfl⟩, rfl⟩
  refine ⟨b * c, B.mul_mem hb hc, Fin.append v v', ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact hv i
    · rw [Fin.append_right]; exact hv' i
  · show _ * _ = _
    rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 2
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OmegaConstruction
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.OmegaConstruction.Om :
    (O : Type) → [inst : CommRing O] → [IsLocalRing O] → ℕ → Type :=
    fun (O : Type) [CommRing O] [IsLocalRing O] (m : ℕ) ↦ O ⧸ IsLocalRing.maximalIdeal O ^ m

noncomputable def UpperTheory.Reformulated.B.OmegaConstruction.red :
    {O : Type} →
      [inst : CommRing O] →
        [inst_1 : IsLocalRing O] →
          {n : ℕ} → (m : ℕ) → Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.OmegaConstruction.Om O m) :=
    fun {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (Z : Matrix (Fin n) (Fin n) O) ↦
      Z.map (⇑(Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ m)) : O → O ⧸ IsLocalRing.maximalIdeal O ^ m)

theorem UpperTheory.Reformulated.B.OmegaConstruction.red_sub :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O),
      UpperTheory.Reformulated.B.OmegaConstruction.red m (A - B) = UpperTheory.Reformulated.B.OmegaConstruction.red m A - UpperTheory.Reformulated.B.OmegaConstruction.red m B := by
  intro O _ _ n m A B
  ext i j
  exact map_sub (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ m)) (A i j) (B i j)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OneLeftCongr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
private noncomputable def UpperTheory.specMapOverOfAlgHom {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A B : Type} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ x) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ x) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact f.comp_algebraMap)

open AlgebraicGeometry CategoryTheory in
private theorem UpperTheory.specMapAlg_comp {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    UpperTheory.specMapOverOfAlgHom x g ≫ UpperTheory.specMapOverOfAlgHom x f = UpperTheory.specMapOverOfAlgHom x (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

open AlgebraicGeometry CategoryTheory in
private theorem UpperTheory.specMap_id {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A : Type} [CommRing A] [Algebra R A] :
    UpperTheory.specMapOverOfAlgHom x (AlgHom.id R A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
private theorem UpperTheory.grpObj_one_left_congr {S : Scheme.{0}} (G : Over S) [GrpObj G]
    {X : Scheme.{0}} {x y : X ⟶ S} (h : x = y) :
    (1 : Over.mk x ⟶ G).left = (1 : Over.mk y ⟶ G).left := by
  subst h
  rfl

theorem UpperTheory.tangent_left_one :
    open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
        ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)
          (v w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) ⟶ G),
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left = (1 : Over.mk x ⟶ G).left →
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ w.left = (1 : Over.mk x ⟶ G).left →
            ∃ u : Spec (CommRingCat.of (TrivSqZeroExt R (R × R))) ⟶ G.left,
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R (R × R)).toRingHom) ≫ u = (1 : Over.mk x ⟶ G).left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom) ≫ u = v.left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ≫ u = w.left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)).toRingHom) ≫ u
                = (v * w).left := by
  open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
  · intro S G _ R _ x v w hv hw
    have hx : Spec.map (CommRingCat.ofHom (algebraMap R R)) ≫ x = x := by
      have : Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ := Spec.map_id _
      rw [this, Category.id_comp]
    have h1 := UpperTheory.grpObj_one_left_congr G hx
    have hv' : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R R) ≫ v = 1 :=
      Over.OverMorphism.ext (hv.trans h1.symm)
    have hw' : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R R) ≫ w = 1 :=
      Over.OverMorphism.ext (hw.trans h1.symm)
    have e0 : (TrivSqZeroExt.map (0 : R →ₗ[R] R)) =
        (Algebra.ofId R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R) := by
      apply AlgHom.ext
      intro a
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    have hv0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (0 : R →ₗ[R] R)) ≫ v = 1 := by
      rw [e0, ← UpperTheory.specMapAlg_comp, Category.assoc, hv', MonObj.comp_one]
    have hw0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (0 : R →ₗ[R] R)) ≫ w = 1 := by
      rw [e0, ← UpperTheory.specMapAlg_comp, Category.assoc, hw', MonObj.comp_one]
    let U : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R (R × R)))) ≫ x) ⟶ G :=
      (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.inl R R R)) ≫ v) *
        (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.inr R R R)) ≫ w)
    have key : ∀ f : (R × R) →ₗ[R] R, UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map f) ≫ U =
        (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (f ∘ₗ LinearMap.inl R R R)) ≫ v) *
          (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (f ∘ₗ LinearMap.inr R R R)) ≫ w) := by
      intro f
      simp only [U, MonObj.comp_mul, ← Category.assoc, UpperTheory.specMapAlg_comp,
        TrivSqZeroExt.map_comp_map]
    have k0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R (R × R)) ≫ U = 1 := by
      simp only [U, MonObj.comp_mul, ← Category.assoc, UpperTheory.specMapAlg_comp,
        TrivSqZeroExt.fstHom_comp_map]
      rw [hv', hw', _root_.mul_one]
    have k1 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.fst R R R)) ≫ U = v := by
      rw [key, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hw0, TrivSqZeroExt.map_id,
        UpperTheory.specMap_id, Category.id_comp, _root_.mul_one]
    have k2 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.snd R R R)) ≫ U = w := by
      rw [key, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hv0, TrivSqZeroExt.map_id,
        UpperTheory.specMap_id, Category.id_comp, _root_.one_mul]
    have k3 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)) ≫ U
        = v * w := by
      rw [key, LinearMap.add_comp, LinearMap.add_comp, LinearMap.fst_comp_inl,
        LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, add_zero, zero_add,
        TrivSqZeroExt.map_id, UpperTheory.specMap_id, Category.id_comp, Category.id_comp]
    exact ⟨U.left, (congrArg CommaMorphism.left k0).trans h1, congrArg CommaMorphism.left k1,
      congrArg CommaMorphism.left k2, congrArg CommaMorphism.left k3⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OpenFix
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.GQ :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Gal(UpperTheory.Reformulated.B.Qi42.Om l/ℚ_[l])

theorem UpperTheory.Reformulated.B.Qi42.open_fix :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] (H : Subgroup (UpperTheory.Reformulated.B.Qi42.GQ v)),
      IsOpen (↑H : Set (UpperTheory.Reformulated.B.Qi42.GQ v)) → (IntermediateField.fixedField H).fixingSubgroup = H := by
  intro v inst H hH
  haveI : IsGalois ℚ_[v] (PadicAlgCl v) := IsAlgClosure.isGalois ℚ_[v] (PadicAlgCl v)
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrbitFinite
section
theorem UpperTheory.Reformulated.B.Qf32.orbit_finite :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {G : Type}
    [inst_2 : Group G] [inst_3 : TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K : Subgroup G),
    IsCompact (↑K : Set G) →
      ∀ (w : V),
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) w = w} →
          {x : V | ∃ k ∈ K, ((ρ : G → V →ₗ[ℂ] V) k : V → V) w = x}.Finite := by
  intro V _ _ G _ _ _ ρ K hK w hw
  have hloc : IsLocallyConstant (fun g : G => ρ g w) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k
    refine ⟨(fun g : G => k⁻¹ * g) ⁻¹' {g : G | ρ g w = w},
      hw.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro g hg
    have hg' : ρ (k⁻¹ * g) w = w := hg
    calc ρ g w = ρ (k * (k⁻¹ * g)) w := by rw [mul_inv_cancel_left]
      _ = ρ k (ρ (k⁻¹ * g) w) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ k w := by rw [hg']
  haveI : CompactSpace (K : Set G) := isCompact_iff_compactSpace.mp hK
  have hfin := (hloc.comp_continuous
    (continuous_subtype_val (p := fun g : G => g ∈ (K : Set G)))).range_finite
  refine hfin.subset ?_
  rintro x ⟨k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrderedFlagDiagonal
section
namespace UpperTheory.Reformulated.B.OrderedFlagDiagonal
abbrev M4 (R : Type) : Type := Matrix (Fin 4) (Fin 4) R

variable {K : Type} [Field K]

theorem ordFlag_diag (c : Fin 4 → K) (hc : Function.Injective c) (X : M4 K)
    (hX : X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (c j))) :
    ∃ P : (M4 K)ˣ, X * (P : M4 K) = (P : M4 K) * Matrix.diagonal c := by
  have hev : ∀ j, Module.End.HasEigenvalue (Matrix.toLin' X) (c j) := by
    intro j
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hX,
      Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  choose v hv using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' X) c hc v hv
  have hU : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin 4) (Fin 4) K) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  obtain ⟨P, hP⟩ := hU
  refine ⟨P, ?_⟩
  rw [hP]
  ext i j
  have h := congrFun (hv j).apply_eq_smul i
  rw [Matrix.toLin'_apply] at h
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end UpperTheory.Reformulated.B.OrderedFlagDiagonal
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PairCases
section
theorem UpperTheory.Reformulated.B.PairCases.pair_cases :
    ∀ {a b c d : @Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)},
      @Eq (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
          (@Insert.insert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
            (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
            (@Multiset.instInsert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) a
            (@Singleton.singleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
              (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
              (@Multiset.instSingleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) b))
          (@Insert.insert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
            (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
            (@Multiset.instInsert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) c
            (@Singleton.singleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
              (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
              (@Multiset.instSingleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) d)) →
        Or
          (And (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) a c)
            (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) b d))
          (And (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) a d)
            (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) b c)) := by
  intro a b c d h
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons] at h
  rcases Multiset.cons_eq_cons.mp h with ⟨h1, h2⟩ | ⟨_, cs, h2, h3⟩
  · exact Or.inl ⟨h1, Multiset.singleton_inj.mp h2⟩
  · exact Or.inr ⟨(Multiset.singleton_eq_cons_iff _ |>.mp h3).1.symm,
      (Multiset.singleton_eq_cons_iff _ |>.mp h2).1⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PairedCharacterCondition
section
noncomputable def UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale :
    Prop :=
    ∀ (K : Type) [inst : Field K] [NumberField K] (V : Type) [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
      (M : Submodule (NumberField.RingOfIntegers K) V),
      Submodule.span K (↑M : Set V) = ⊤ → ∀ (f : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ (↑m : K) • f ∈ M

theorem UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale :
    UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale := by
  intro K _ _ V _ _ _ _ M hM f
  have key : ∀ (c : K), IsIntegral ℤ c → ∀ x ∈ M, c • x ∈ M := by
    intro c hc x hx
    obtain ⟨r, rfl⟩ : ∃ r : NumberField.RingOfIntegers K, algebraMap _ K r = c := ⟨⟨c, hc⟩, rfl⟩
    rw [algebraMap_smul]
    exact M.smul_mem r hx
  have hint : ∀ n : ℤ, IsIntegral ℤ (n : K) := fun n => isIntegral_algebraMap (R := ℤ) (x := n)
  have hf : f ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (x + y) = (b : K) • ((a : K) • x) + (a : K) • ((b : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : K)]
    rw [e]
    exact M.add_mem (key _ (hint b) _ hx) (key _ (hint a) _ hy)
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have halg : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨b, hb, hc⟩ := halg.exists_integral_multiple
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (c • x) = (b • c) • ((a : K) • x) := by
      rw [smul_smul, smul_smul, Int.cast_mul, zsmul_eq_mul]
      congr 1
      ring
    rw [e]
    exact key _ hc _ hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PartialFiltrationCoeff
section
theorem UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff :
    ∀ {O σ : Type} [inst : CommRing O]
    [inst_1 : IsLocalRing O] (M : ℕ),
    ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ M,
      ∀ (n : σ →₀ ℕ),
        (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f ∈
          IsLocalRing.maximalIdeal O ^ (M - (Finsupp.degree : (σ →₀ ℕ) → ℕ) n) := by
  intro O σ _ _ M
  classical
  induction M with
  | zero =>
    intro f _ n
    simp
  | succ M ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb n
      rw [MvPowerSeries.coeff_mul]
      refine Ideal.sum_mem _ ?_
      rintro ⟨p, q⟩ hpq
      have hsum : p + q = n := by simpa using hpq
      have hdeg : Finsupp.degree p + Finsupp.degree q = Finsupp.degree n := by
        rw [← hsum, map_add (f := _)]
      have hp := ih a ha p
      by_cases hq : q = 0
      · subst hq
        have hb0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) b ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
          intro hu
          exact hb (MvPowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hu))
        have hmul := Ideal.mul_mem_mul hp hb0
        rw [← pow_succ] at hmul
        exact Ideal.pow_le_pow_right (by omega) hmul
      · have hq' : Finsupp.degree q ≠ 0 := fun h => hq ((Finsupp.degree_eq_zero_iff q).mp h)
        exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) hp)
    · intro x y hx hy n
      rw [map_add (f := _)]
      exact Ideal.add_mem _ (hx n) (hy n)
end

