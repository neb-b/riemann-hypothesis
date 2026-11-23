module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjDefs
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def HasStableRangeOne (A : Type) [CommRing A] : Prop :=
  ∀ a b x y : A, a * x + b * y = 1 → ∃ t, IsUnit (a + t * b)

def AdeleStableRankOne : Prop := ∀ (F : Type) [Field F] [NumberField F], HasStableRangeOne (AF F)

def ElimSR1 : Prop :=
  ∀ (A : Type) [CommRing A], HasStableRangeOne A → ∀ (k : ℕ) (X : GL (Fin k) A),
    X ∈ Subgroup.closure ({g : GL (Fin k) A | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = Matrix.diagonal d})

def TransvHaar : Prop :=
  ∀ (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A] (k : ℕ)
    (i j : Fin k), i ≠ j → ∀ (c : A) (μ : Measure (Fin k → A)), μ.IsAddHaarMeasure →
      μ.map (Matrix.mulVec (Matrix.transvection i j c)) = μ

def OrthInv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (G X : Matrix (Fin k) (Fin k) (AF F)),
    IsUnit G.det → X.transpose * G * X = G →
    ∀ μ : Measure (Fin k → AF F), μ.IsAddHaarMeasure → μ.map (Matrix.mulVec X) = μ

def VMod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (g : HA (AF F) σ J) (μ : Measure (Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure →
      μ.map (lin (AF F) σ J g) = μ

end PI.VolSemiDirect.W.Cj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Closed
section
noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem continuous_lin [IsTopologicalRing (R ⊗[F] E)] (x : Fin n → R ⊗[F] E) :
    Continuous fun g : HA R σ J => lin R σ J g x := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  simp only [lin, Matrix.mulVecLin_apply]
  exact hm.matrix_mulVec continuous_const

theorem exists_proj_mat (K : Submodule E (Fin n → E)) :
    ∃ P : Matrix (Fin n) (Fin n) E, (∀ x, P *ᵥ x ∈ K) ∧ ∀ x ∈ K, P *ᵥ x = x := by
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl K
  refine ⟨LinearMap.toMatrix' (K.subtype ∘ₗ Submodule.linearProjOfIsCompl K K' hK), fun x => ?_, fun x hx => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    exact (Submodule.linearProjOfIsCompl K K' hK x).2
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply]
    have := Submodule.linearProjOfIsCompl_apply_left hK ⟨x, hx⟩
    exact congrArg Subtype.val this

variable {R}

theorem ratV_mem_spanR {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Y '' s)) : ratV (F := F) R x ∈ spanR (F := F) R Y s := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero =>
    have h0 : ratV (F := F) R (0 : Fin n → E) = 0 := by
      funext i
      simp [ratV]
    rw [h0]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have h0 : ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
      funext i
      simp [ratV]
    rw [h0]
    exact add_mem hx hy
  | smul c x _ hx =>
    have h0 : ratV (F := F) R (c • x) = inclR (F := F) R c • ratV (F := F) R x := by
      funext i
      simp [ratV]
    rw [h0]
    exact Submodule.smul_mem _ _ hx

theorem ratV_mulVec (P : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    ratV (F := F) R (P *ᵥ x) = (P.map (inclR (F := F) R)) *ᵥ ratV (F := F) R x := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ratV, Matrix.mulVec, dotProduct, map_sum]

theorem mem_spanR_iff {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m))
    (P : Matrix (Fin n) (Fin n) E) (hP1 : ∀ x, P *ᵥ x ∈ Submodule.span E (Y '' s))
    (hP2 : ∀ x ∈ Submodule.span E (Y '' s), P *ᵥ x = x) (v : Fin n → R ⊗[F] E) :
    v ∈ spanR (F := F) R Y s ↔ (P.map (inclR (F := F) R)) *ᵥ v = v := by
  have hfix : ∀ a ∈ s, (P.map (inclR (F := F) R)) *ᵥ ratV (F := F) R (Y a) = ratV (F := F) R (Y a) := by
    intro a ha
    rw [← ratV_mulVec, hP2 _ (Submodule.subset_span ⟨a, ha, rfl⟩)]
  have hsingle : ∀ j : Fin n, ratV (F := F) R (Pi.single j (1 : E)) = Pi.single j 1 := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij
      simp [ratV]
    · simp [ratV, Pi.single_apply, hij]
  constructor
  · intro hv
    have hle : spanR (F := F) R Y s ≤ LinearMap.eqLocus (Matrix.mulVecLin (P.map (inclR (F := F) R))) LinearMap.id := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      exact hfix a ha
    exact hle hv
  · intro h
    rw [← h]
    have hv : v = ∑ j, v j • Pi.single j (1 : R ⊗[F] E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ ?_
    have := ratV_mem_spanR (F := F) (R := R) Y s _ (hP1 (Pi.single j 1))
    rwa [ratV_mulVec, hsingle] at this

theorem isClosed_spanR [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) :
    IsClosed (spanR (F := F) R Y s : Set (Fin n → R ⊗[F] E)) := by
  obtain ⟨P, h1, h2⟩ := exists_proj_mat (Submodule.span E (Y '' s))
  have hset : (spanR (F := F) R Y s : Set (Fin n → R ⊗[F] E)) =
      {v | (P.map (inclR (F := F) R)) *ᵥ v = v} := by
    ext v
    exact mem_spanR_iff (F := F) (R := R) Y s P h1 h2 v
  rw [hset]
  exact isClosed_eq (continuous_const.matrix_mulVec continuous_id) continuous_id

variable (R)

theorem isClosed_stabT [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {a : ℕ}
    (X : Fin a → Fin n → E) : IsClosed (stabT R σ J X : Set (HA R σ J)) := by
  have hset : (stabT R σ J X : Set (HA R σ J)) =
      ⋂ b, {g | lin R σ J g (ratV (F := F) R (X b)) = ratV (F := F) R (X b)} := by
    ext g
    simp [mem_stabT]
  rw [hset]
  exact isClosed_iInter fun b => isClosed_eq (continuous_lin R σ J _) continuous_const

end Gen

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.EqZeroOfMemNbhdA
section
noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix

section Adele

variable (F : Type) [Field F] [NumberField F]

theorem continuous_norm_inf : Continuous fun y : InfiniteAdeleRing F => ‖y‖ := by
  show Continuous fun y : InfiniteAdeleRing F => ∏ v, ‖y v‖ ^ v.mult
  exact continuous_finsetProd _ fun v _ => ((continuous_apply v).norm).pow _

def nbhdA : Set (AF F) := {x | ‖x.1‖ < 1 ∧ x.2 ∈ PI.AdCpctDenWork.intAd F}

theorem isOpen_nbhdA : IsOpen (nbhdA F) :=
  (isOpen_lt ((continuous_norm_inf F).comp continuous_fst) continuous_const).inter
    (PI.AdCpctDenWork.isOpen_intAd.preimage continuous_snd)

theorem eq_zero_of_mem_nbhdA (f : F) (hf : algebraMap F (AF F) f ∈ nbhdA F) : f = 0 := by
  obtain ⟨h1, h2⟩ := hf
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F f ≤ 1 := by
    intro v
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    have h3 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) f) v ∈ v.adicCompletionIntegers F := h2 v
    rw [FiniteAdeleRing.algebraMap_apply] at h3
    exact h3
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ hint
  have h4 : ‖algebraMap F (InfiniteAdeleRing F) f‖ < 1 := h1
  rw [InfiniteAdeleRing.coe_norm_eq_abs_norm] at h4
  by_contra hf0
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hf0
    rw [← hr, map_zero]
  have h5 : (1 : ℚ) ≤ |Algebra.norm ℚ ((r : 𝓞 F) : F)| := by
    have := Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hr0)
    rw [← Algebra.coe_norm_int]
    exact_mod_cast this
  have h6 : ((r : 𝓞 F) : F) = f := hr
  rw [h6] at h5
  have h4' : |Algebra.norm ℚ f| < 1 := by exact_mod_cast h4
  linarith

theorem zero_mem_nbhdA : (0 : AF F) ∈ nbhdA F := by
  have h : algebraMap F (AF F) 0 ∈ nbhdA F := by
    refine ⟨?_, fun v => ?_⟩
    · show ‖algebraMap F (InfiniteAdeleRing F) 0‖ < 1
      rw [InfiniteAdeleRing.coe_norm_eq_abs_norm]
      simp
    · show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0) v ∈ v.adicCompletionIntegers F
      rw [map_zero]
      exact zero_mem _
  rwa [map_zero] at h

end Adele

section Tens

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [Module.Finite F E]

theorem exists_nbhd_tens : ∃ U : Set (AF F ⊗[F] E), IsOpen U ∧ (0 : AF F ⊗[F] E) ∈ U ∧
    ∀ e : E, inclR (F := F) (AF F) e ∈ U → e = 0 := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  refine ⟨⋂ i, (B.coord i) ⁻¹' nbhdA F, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun i =>
      (isOpen_nbhdA F).preimage (IsModuleTopology.continuous_of_linearMap (B.coord i))
  · simp only [Set.mem_iInter, Set.mem_preimage, map_zero]
    exact fun _ => zero_mem_nbhdA F
  · intro e he
    simp only [Set.mem_iInter, Set.mem_preimage] at he
    have hc : ∀ i, b.repr e i = 0 := by
      intro i
      apply eq_zero_of_mem_nbhdA F
      have := he i
      have hco : B.coord i (inclR (F := F) (AF F) e) = algebraMap F (AF F) (b.repr e i) := by
        simp [B, inclR, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]
      rwa [hco] at this
    have : b.repr e = 0 := Finsupp.ext hc
    simpa using this

end Tens

theorem discHA_of (hT : TensTop) : DiscHA := by
  intro F E _ _ _ _ _ σ hCM M J _
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨h1, -, -, -⟩ := hT F E
  constructor
  · haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
    haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
    haveI : Countable (GL (Fin M) E) :=
      (Units.val_injective (α := Matrix (Fin M) (Fin M) E)).countable
    have hS : (HFin (AF F) σ J : Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      rw [HFin, Subgroup.coe_map]
      exact (Set.to_countable _).image _
    haveI : Countable (HFin (AF F) σ J) := hS.to_subtype
    let φ : HFinIn (AF F) σ J → HFin (AF F) σ J := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
    have hφ : Function.Injective φ := by
      intro x y h
      simp only [φ, Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    exact hφ.countable
  · obtain ⟨U, hUo, hU0, hUe⟩ := exists_nbhd_tens F E
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 x.2)
    let V : Set (HR (AF F) σ J) := {g | ∀ i j,
      ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j -
        ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ U}
    have hVo : IsOpen V := by
      have hc : Continuous fun g : HR (AF F) σ J =>
          ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
        Units.continuous_val.comp continuous_subtype_val
      have : V = ⋂ i, ⋂ j, (fun g : HR (AF F) σ J =>
          ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j -
            ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j) ⁻¹' U := by
        ext g
        simp [V]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hUo.preimage (((continuous_apply j).comp ((continuous_apply i).comp hc)).sub
          continuous_const)
    rw [isOpen_induced_iff]
    refine ⟨V, hVo, Set.ext fun y => ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 y.2)
      have hent : ∀ i j, (δ : Matrix (Fin M) (Fin M) E) i j = (γ : Matrix (Fin M) (Fin M) E) i j := by
        intro i j
        have h := hy i j
        rw [← hδ, ← hγ] at h
        have h' : inclR (F := F) (AF F) ((δ : Matrix (Fin M) (Fin M) E) i j -
            (γ : Matrix (Fin M) (Fin M) E) i j) ∈ U := by
          rw [map_sub]
          exact h
        exact sub_eq_zero.1 (hUe _ h')
      have hm : δ = γ := Units.ext (Matrix.ext hent)
      apply Subtype.ext
      apply Subtype.ext
      rw [← hδ, ← hγ, hm]
    · rintro rfl i j
      simp only [sub_self]
      exact hU0

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.FundamentalDomainExists
section
noncomputable section

namespace PI.VolSemiDirect.W

open MeasureTheory

theorem exists_sfd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Λ : Subgroup G)
    [DiscreteTopology Λ] :
    ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ ∀ x : G, ∃! γ : Λ, γ • x ∈ 𝓕 := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Λ))
  have hV1 : ∀ γ : Λ, (γ : G) ∈ V ↔ γ = 1 := fun γ => Set.ext_iff.mp hV γ
  have h1V : (1 : G) ∈ V := (hV1 1).mpr rfl
  obtain ⟨W, hWo, hW1, hWV⟩ := exists_open_nhds_one_split (hVo.mem_nhds h1V)
  obtain ⟨U, hUo, hU1, hUinv, hUV⟩ : ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ (∀ g ∈ U, g⁻¹ ∈ U) ∧
      ∀ a ∈ U, ∀ b ∈ U, a * b⁻¹ ∈ V :=
    ⟨W ∩ (fun g => g⁻¹) ⁻¹' W, hWo.inter (hWo.preimage continuous_inv), ⟨hW1, by simpa using hW1⟩,
      fun g hg => ⟨hg.2, by simpa using hg.1⟩, fun a ha b hb => hWV a ha.1 _ hb.2⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq G

  have hB : ∀ x : G, ∃ n, x * (d n)⁻¹ ∈ U := by
    intro x
    obtain ⟨n, hn⟩ := hd.exists_mem_open
      (hUo.preimage (continuous_id.mul continuous_const) : IsOpen ((fun y => y * x⁻¹) ⁻¹' U))
      ⟨x, by simpa using hU1⟩
    refine ⟨n, ?_⟩
    have := hUinv _ hn
    simpa [mul_inv_rev] using this

  have hBu : ∀ (n : ℕ) (γ γ' : Λ) (x : G), (γ : G) * x * (d n)⁻¹ ∈ U →
      (γ' : G) * x * (d n)⁻¹ ∈ U → γ = γ' := by
    intro n γ γ' x h h'
    have hm := hUV _ h _ h'
    have : ((γ * γ'⁻¹ : Λ) : G) ∈ V := by
      convert hm using 1
      push_cast
      group
    rw [hV1, mul_inv_eq_one] at this
    exact this

  obtain ⟨S, hS, hSo⟩ : ∃ S : ℕ → Set G, (∀ m x, x ∈ S m ↔ ∃ γ : Λ, (γ : G) * x * (d m)⁻¹ ∈ U) ∧
      ∀ m, IsOpen (S m) :=
    ⟨fun m => ⋃ γ : Λ, (fun x => (γ : G) * x * (d m)⁻¹) ⁻¹' U, fun m x => by simp,
      fun m => isOpen_iUnion fun γ =>
        hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)⟩
  have hinv : ∀ (γ : Λ) (y : G) (m : ℕ), (γ : G) * y ∈ S m ↔ y ∈ S m := by
    intro γ y m
    rw [hS, hS]
    constructor
    · rintro ⟨δ, hδ⟩
      exact ⟨δ * γ, by push_cast; simpa [mul_assoc] using hδ⟩
    · rintro ⟨δ, hδ⟩
      exact ⟨δ * γ⁻¹, by push_cast; simpa [mul_assoc] using hδ⟩
  obtain ⟨F, hF, hFm⟩ : ∃ F : Set G, (∀ y, y ∈ F ↔ ∃ n, y * (d n)⁻¹ ∈ U ∧ ∀ m < n, y ∉ S m) ∧
      MeasurableSet F := by
    refine ⟨⋃ n, ((fun x => x * (d n)⁻¹) ⁻¹' U \ ⋃ m, ⋃ (_ : m < n), S m), fun y => ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_diff, Set.mem_preimage, not_exists]
    · exact MeasurableSet.iUnion fun n =>
        (hUo.preimage (continuous_id.mul continuous_const)).measurableSet.diff
          (isOpen_iUnion fun m => isOpen_iUnion fun _ => hSo m).measurableSet
  refine ⟨F, hFm, fun x => ?_⟩
  have hex : ∃ n, x ∈ S n := by
    obtain ⟨n, hn⟩ := hB x
    exact ⟨n, (hS n x).mpr ⟨1, by simpa using hn⟩⟩
  classical
  obtain ⟨n0, hn0x, hmin⟩ : ∃ n0, x ∈ S n0 ∧ ∀ m < n0, x ∉ S m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  obtain ⟨γ, hγ⟩ := (hS n0 x).mp hn0x
  refine ⟨γ, ?_, ?_⟩
  · change (γ : G) * x ∈ F
    rw [hF]
    exact ⟨n0, hγ, fun m hm h => hmin m hm ((hinv γ x m).mp h)⟩
  · intro γ' hγ'
    change (γ' : G) * x ∈ F at hγ'
    rw [hF] at hγ'
    obtain ⟨n, hn, hnmin⟩ := hγ'
    have hxn : x ∈ S n := (hS n x).mpr ⟨γ', hn⟩
    have hn0 : n = n0 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        exact hnmin n0 hlt ((hinv γ' x n0).mpr hn0x)
      · exact not_lt.mp fun h => hmin n h hxn
    rw [hn0] at hn
    exact hBu n0 γ' γ x hn hγ

theorem exists_fd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Λ : Subgroup G)
    [DiscreteTopology Λ] :
    ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ ∀ μ : Measure G, IsFundamentalDomain Λ 𝓕 μ := by
  obtain ⟨F, hF, hex⟩ := exists_sfd Λ
  exact ⟨F, hF, fun μ => IsFundamentalDomain.mk' hF.nullMeasurableSet hex⟩

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SemiDefs
section
noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SubgroupLocallyCompactHolds
section
noncomputable section

namespace PI.VolSemiDirect.W

theorem subgroup_locally_compact_holds : SubLCSC := by
  intro X _ _ Γ K hX hK hΓc hΓd
  obtain ⟨hlc, hsc, ht2, htg⟩ := hX
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI := htg
  haveI := hΓc
  haveI := hΓd
  let f : ratG Γ K → Γ := fun x => ⟨(x : K).1, (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 x.2)).1⟩
  refine ⟨⟨hK.isClosedEmbedding_subtypeVal.locallyCompactSpace, Topology.IsEmbedding.subtypeVal.secondCountableTopology,
    inferInstance, inferInstance⟩, ?_, ?_⟩
  · have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg (fun y : Γ => (y : X)) h
      exact h'
    exact hf.countable
  · have hcont : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hemb : Topology.IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp hcont continuous_subtype_val
      show Topology.IsEmbedding (fun x : ratG Γ K => ((x : K) : X))
      exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact hemb.discreteTopology

end PI.VolSemiDirect.W
end
end

