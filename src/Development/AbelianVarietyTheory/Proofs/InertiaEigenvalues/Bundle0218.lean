module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CyclotomicFrobeniusPowerSeriesXEqMulQuotient
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CompactRepField

open Polynomial IntermediateField

theorem exists_mem_adjoin_simple (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (j : Ω →+* PadicAlgCl l) (x : PadicAlgCl l) : ∃ y : Ω, x ∈ ℚ_[l]⟮j y⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hfin : ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint x)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖x - y‖ < ‖x - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  obtain ⟨y, hy⟩ := (GlobalTheory.denseRange_of_isAlgClosed_padicAlgCl l Ω j).exists_mem_open hop
    ⟨x, by
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
      exact fun x' h => h.2⟩
  refine ⟨y, IsKrasner.krasner (minpoly.irreducible (hint x)).separable (IsAlgClosed.splits _)
    (hint _) fun x' h1 h2 => ?_⟩
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hy
  exact hy x' ⟨h1, h2⟩

theorem exists_countable_family (l : ℕ) [Fact l.Prime] :
    ∃ (ι : Type) (_ : Countable ι) (K : ι → IntermediateField ℚ_[l] (PadicAlgCl l)),
      (∀ i, FiniteDimensional ℚ_[l] (K i)) ∧
      ∀ s : Set (PadicAlgCl l), s.Finite → ∃ i, s ⊆ K i := by
  classical
  haveI halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Countable (AlgebraicClosure ℚ) := by
    have h : {x : AlgebraicClosure ℚ | IsAlgebraic ℚ x}.Countable := Algebraic.countable ℚ _
    exact Set.countable_univ_iff.1 (h.mono fun x _ => halg.isAlgebraic x)
  let j : AlgebraicClosure ℚ →+* PadicAlgCl l :=
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := PadicAlgCl l)).toRingHom
  refine ⟨Finset (AlgebraicClosure ℚ), inferInstance,
    fun S => IntermediateField.adjoin ℚ_[l] (j '' (S : Set _)), fun S => ?_, fun s hs => ?_⟩
  · haveI : Finite (j '' (S : Set (AlgebraicClosure ℚ))) := (S.finite_toSet.image j).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  · choose y hy using exists_mem_adjoin_simple l (AlgebraicClosure ℚ) j
    refine ⟨(hs.image y).toFinset, fun x hx => ?_⟩
    refine IntermediateField.adjoin.mono _ _ _ ?_ (hy x)
    rw [Set.singleton_subset_iff]
    exact ⟨y x, by simpa using ⟨x, hx, rfl⟩, rfl⟩

def entrySubgroup {F E G : Type} [Field F] [Field E] [Algebra F E] [Group G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) E) (K : IntermediateField F E) : Subgroup G where
  carrier := {g | ∀ i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K ∧
    (r g⁻¹ : Matrix (Fin a) (Fin a) E) i j ∈ K}
  one_mem' := fun i j => by
    have : (r 1 : Matrix (Fin a) (Fin a) E) i j ∈ K := by
      rw [map_one, Units.val_one, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    exact ⟨this, by rwa [inv_one]⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨sum_mem fun k _ => mul_mem (hg i k).1 (hh k j).1,
      sum_mem fun k _ => mul_mem (hh i k).2 (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem exists_finiteDimensional_entries_mem (l : ℕ) [Fact l.Prime] (G : Type) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (n : ℕ)
    (r : G →* Matrix.GeneralLinearGroup (Fin n) (PadicAlgCl l))
    (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧
      ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K := by
  obtain ⟨ι, _, K, hK, hcov⟩ := exists_countable_family l
  have hKcl : ∀ m, IsClosed (K m : Set (PadicAlgCl l)) := fun m =>
    haveI : FiniteDimensional ℚ_[l] (K m).toSubalgebra.toSubmodule := hK m
    Submodule.closed_of_finiteDimensional (K m).toSubalgebra.toSubmodule
  have hcl : ∀ m, IsClosed (entrySubgroup r (K m) : Set G) := fun m => by
    have : (entrySubgroup r (K m) : Set G) = ⋂ i, ⋂ j,
        ((fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m) ∩
         (fun g => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m)) := by
      ext g
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      ((hKcl m).preimage (hr i j)).inter ((hKcl m).preimage ((hr i j).comp continuous_inv))
  have hun : ⋃ m, (entrySubgroup r (K m) : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨m, hm⟩ := hcov
      (Set.range (fun p : Fin n × Fin n => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2) ∪
       Set.range (fun p : Fin n × Fin n => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2))
      ((Set.finite_range _).union (Set.finite_range _))
    exact Set.mem_iUnion.2 ⟨m, fun i j =>
      ⟨hm (Or.inl ⟨(i, j), rfl⟩), hm (Or.inr ⟨(i, j), rfl⟩)⟩⟩
  obtain ⟨m, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (entrySubgroup r (K m) : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (G ⧸ entrySubgroup r (K m)) := Subgroup.quotient_finite_of_isOpen _ hop
  let s : Set (PadicAlgCl l) := Set.range fun p : (G ⧸ entrySubgroup r (K m)) × Fin n × Fin n =>
    (r p.1.out : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.2.1 p.2.2
  haveI : Finite s := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  haveI := hK m
  refine ⟨IntermediateField.adjoin ℚ_[l] s ⊔ K m, inferInstance, fun g i j => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (entrySubgroup r (K m)) g
  have hg : g = (g : G ⧸ entrySubgroup r (K m)).out * (h : G)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, map_mul, Units.val_mul, Matrix.mul_apply]
  refine sum_mem fun k _ => mul_mem ?_ ?_
  · exact (le_sup_left : IntermediateField.adjoin ℚ_[l] s ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(g, i, k), rfl⟩)
  · exact (le_sup_right : K m ≤ _) (h.2 k j).2

theorem exists_finExt_entries_mem :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (a : ℕ) (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l)), Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ L₀ : FinExt l, ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := by
  intro l _ G _ _ _ _ _ a r hr L₀
  obtain ⟨K, hK, h⟩ := exists_finiteDimensional_entries_mem l G a r
    fun i j => hr.matrix_elem i j
  haveI := L₀.2
  exact ⟨⟨L₀.1 ⊔ K, inferInstance⟩, le_sup_left, fun g i j =>
    (le_sup_right : K ≤ L₀.1 ⊔ K) (h g i j)⟩

end GlobalTheory.CompactRepField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAdicModuleIff
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open Topology Filter

namespace GlobalTheory

private lemma mem_span_pow_smul_iff_exists_pow_smul {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] (n : ℕ) (x : M) :
    x ∈ (Ideal.span {a}) ^ n • (⊤ : Submodule R M) ↔ ∃ y : M, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp [eq_comm]

theorem continuous_adicModule_iff {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] {G : Type} [TopologicalSpace G] (f : G → M) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) f ↔
      ∀ (g : G) (n : ℕ), ∀ᶠ h in 𝓝 g, ∃ y : M, f h - f g = a ^ n • y := by
  let _ : TopologicalSpace R := (Ideal.span {a}).ringFilterBasis.topology
  let _ : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M
  have hB : ∀ y : M, (𝓝 y).HasBasis
      (fun V : Set M => ∃ n : ℕ, V = ↑((Ideal.span {a}) ^ n • (⊤ : Submodule R M)))
      (fun V => (fun z => y + z) '' V) := fun y =>
    ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis
      ((Ideal.span {a}).adic_module_basis M)).toAddGroupFilterBasis.nhds_hasBasis y
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun g => ?_
  refine ((hB (f g)).tendsto_right_iff).trans ⟨fun H n => ?_, fun H V hV => ?_⟩
  · filter_upwards [H _ ⟨n, rfl⟩] with h hh
    obtain ⟨z, hz, hzh⟩ := hh
    obtain ⟨y, rfl⟩ := (mem_span_pow_smul_iff_exists_pow_smul a n z).1 hz
    beta_reduce at hzh
    exact ⟨y, by rw [← hzh, add_sub_cancel_left]⟩
  · obtain ⟨n, rfl⟩ := hV
    filter_upwards [H n] with h hh
    obtain ⟨y, hy⟩ := hh
    exact ⟨a ^ n • y, (mem_span_pow_smul_iff_exists_pow_smul a n _).2 ⟨y, rfl⟩, by
      show f g + a ^ n • y = f h
      rw [← hy]; abel⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupOneCocyclesAnticommUpToCoboundary
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

section General

variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] [TopologicalSpace LL]
  [IsTopologicalRing LL]
  {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousConstSMul LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [TopologicalSpace V'] [ContinuousAdd V']
  [ContinuousConstSMul LL V']

theorem cupAnti_cob_of_flip (χ : G →* LLˣ) (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (m : V →ₗ[LL] V' →ₗ[LL] LL) (hm : Continuous fun p : V × V' => m p.1 p.2)
    (hχ : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : LLˣ) : LL) * m x y)
    {a : G → V} (ha : a ∈ continuousCocycles ρ) {b : G → V'} (hb : b ∈ continuousCocycles ρ')
    (h : ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ m.flip b a) :
    ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ' m a b := by
  obtain ⟨f, hf, hfe⟩ := h
  obtain ⟨hac, ha⟩ := ha
  obtain ⟨hbc, hb⟩ := hb
  refine ⟨fun g => -(m (a g) (b g)) - f g, ((hm.comp (hac.prodMk hbc)).neg).sub hf, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  have h1 := congrFun hfe (g, h)
  have h2 := hχ g (a h) (b h)
  simp only [ReciprocityTheory.Def.d1, charRep, cupL, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    ha, hb, map_add, LinearMap.add_apply] at h1 ⊢
  linear_combination -h1 + h2

theorem cupAnti_cob_of_left (χ : G →* LLˣ) (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (m : V →ₗ[LL] V' →ₗ[LL] LL) (hm : Continuous fun p : V × V' => m p.1 p.2)
    (hχ : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : LLˣ) : LL) * m x y)
    {a : G → V} (ha : a ∈ Formalism.WeaklyAdmissibleFiltrations.B1 ρ) {b : G → V'} (hb : b ∈ continuousCocycles ρ') :
    ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ' m a b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨hbc, hb⟩ := hb
  refine ⟨fun g => m x (b g), hm.comp (continuous_const.prodMk hbc), ?_⟩
  funext y
  obtain ⟨g, h⟩ := y
  have h2 := hχ g x (b h)
  simp only [ReciprocityTheory.Def.d1, charRep, cupL, cob, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, LinearMap.pi_apply,
    hb, map_add, map_sub, LinearMap.sub_apply]
  linear_combination -h2

end General

theorem cupL_anticomm_cobL : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, (CobL (P.PD K) (cupL A'.ρ m a b) ↔ CobL (P.PD K) (cupL A.ρ m.flip b a)) ∧ (a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ → CobL (P.PD K) (cupL A'.ρ m a b)) := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m hm a ha b hb
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  have hc : Continuous fun p : A.V × A'.V => m p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left m
  have hc' : Continuous fun p : A'.V × A.V => m.flip p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left m.flip
  have hχ := hm.1
  have hχ' : ∀ g x y, m.flip (A'.ρ g x) (A.ρ g y) =
      ((cycLL (P.PD K) LL g : LLˣ) : LL) * m.flip x y := fun g x y => hχ g y x
  refine ⟨⟨fun h => cupAnti_cob_of_flip _ A'.ρ A.ρ m.flip hc' hχ' hb ha h,
    fun h => cupAnti_cob_of_flip _ A.ρ A'.ρ m hc hχ ha hb h⟩, ?_⟩
  rintro (h | h)
  · exact cupAnti_cob_of_left _ A.ρ A'.ρ m hc hχ h hb
  · exact cupAnti_cob_of_flip _ A.ρ A'.ρ m hc hχ ha hb
      (cupAnti_cob_of_left _ A'.ρ A.ρ m.flip hc' hχ' h ha)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem cyc_eq_binomialSeries (c : ℤ_[l]) : cyc l O c = PowerSeries.binomialSeries O c - 1 :=
  Series.cyc_eq l O c

theorem act_X (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := PowerSeries.substAlgHom_X _

theorem act_apply (c : ℤ_[l]) (a : PowerSeries O) :
    act l O c a = PowerSeries.subst (cyc l O c) a :=
  congrFun (PowerSeries.coe_substAlgHom _) a

theorem act_eq_gam (c : ℤ_[l]) : act l O c = GlobalTheory.Fon.gam O c :=
  Series.act_eq l O c

theorem act_act (c c' : ℤ_[l]) (a : PowerSeries O) :
    act l O c (act l O c' a) = act l O (c * c') a := by
  simp only [act_eq_gam, GlobalTheory.Fon.gam_mul]

theorem act_one (a : PowerSeries O) : act l O 1 a = a := by
  rw [act_eq_gam, GlobalTheory.Fon.gam_one]

theorem cyc_natCast (k : ℕ) : cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1 := by
  rw [cyc_eq_binomialSeries, PowerSeries.binomialSeries_nat]

theorem coeff_one_cyc (c : ℤ_[l]) : PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c := by
  rw [cyc_eq_binomialSeries, ← GlobalTheory.Fon.gam_X, GlobalTheory.Fon.coeff_one_gam_X]

theorem act_pow_sub_one (c : ℤ_[l]) (k : ℕ) :
    act l O c ((1 + PowerSeries.X) ^ k - 1) =
      PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) := by
  rw [← cyc_natCast l O k, ← act_apply, ← act_X l O c, ← act_X l O (k : ℤ_[l]), act_act, act_act,
    mul_comm]

theorem act_laws : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], (∀ c, act l O c PowerSeries.X = cyc l O c) ∧ (∀ c c' a, act l O c (act l O c' a) = act l O (c * c') a) ∧ (∀ a, act l O 1 a = a) ∧ (∀ k : ℕ, cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1) ∧ (∀ c, PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c) ∧ ∀ (c : ℤ_[l]) (k : ℕ), act l O c ((1 + PowerSeries.X) ^ k - 1) = PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) :=
  fun l _ O _ _ => ⟨act_X l O, act_act l O, act_one l O, cyc_natCast l O, coeff_one_cyc l O,
    act_pow_sub_one l O⟩

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeStableTwistedPairing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualLat

variable {LL O V W : Type} [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [FiniteDimensional LL V]
  [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W] [FiniteDimensional LL W]

theorem exists_dual (m : V →ₗ[LL] W →ₗ[LL] LL)
    (h3 : ∀ y : W, (∀ x : V, m x y = 0) → y = 0)
    (h4 : finrank LL V = finrank LL W)
    (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) :
    ∃ T' : Submodule O W, T'.FG ∧ Module.Free O T' ∧ Submodule.span LL (T' : Set W) = ⊤ ∧
      (∀ y, y ∈ T' ↔ ∀ x ∈ T, ∃ a, m x y = algebraMap O LL a) ∧
      (∀ x, x ∈ T ↔ ∀ y ∈ T', ∃ a, m x y = algebraMap O LL a) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let b := Module.Free.chooseBasis O T
  let bV0 : Module.Free.ChooseBasisIndex O T → V := fun i => (b i : V)
  have hTspan : Submodule.span O (Set.range bV0) = T := by
    rw [show bV0 = T.subtype ∘ b from rfl, Set.range_comp, Submodule.span_image, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hliO : LinearIndependent O bV0 := b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hliL : LinearIndependent LL bV0 := (LinearIndependent.iff_fractionRing O LL).mp hliO
  have hspL : ⊤ ≤ Submodule.span LL (Set.range bV0) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← hTspan] at hx
    exact Submodule.span_le_restrictScalars O LL _ hx
  let bV := Basis.mk hliL hspL
  have hbV : ∀ i, bV i = bV0 i := fun i => Basis.mk_apply hliL hspL i
  let φ : W →ₗ[LL] Module.Dual LL V := m.flip
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact h3 y (fun x => by simpa [φ] using LinearMap.congr_fun hy x)
  have hdim : finrank LL W = finrank LL (Module.Dual LL V) := by
    rw [Subspace.dual_finrank_eq, h4]
  let e : W ≃ₗ[LL] Module.Dual LL V := LinearMap.linearEquivOfInjective φ hφ hdim
  let f' := bV.dualBasis.map e.symm
  have key1 : ∀ x j, m x (f' j) = bV.repr x j := by
    intro x j
    have h : φ (f' j) = bV.dualBasis j := by
      show e (e.symm (bV.dualBasis j)) = bV.dualBasis j
      exact e.apply_symm_apply _
    calc m x (f' j) = φ (f' j) x := rfl
      _ = bV.dualBasis j x := by rw [h]
      _ = bV.repr x j := Basis.dualBasis_apply _ _ _
  have key2 : ∀ i y, m (bV i) y = f'.repr y i := by
    intro i y
    have : m (bV i) = f'.coord i := f'.ext (fun j => by
      rw [key1, Basis.coord_apply, Basis.repr_self, Basis.repr_self, Finsupp.single_apply,
        Finsupp.single_apply]
      simp only [eq_comm])
    rw [this, Basis.coord_apply]
  haveI : IsTorsionFree O LL := inferInstance
  refine ⟨Submodule.span O (Set.range f'), Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_, ?_⟩
  · exact Module.Free.of_basis (Basis.span ((LinearIndependent.iff_fractionRing O LL).mpr f'.linearIndependent))
  · rw [Submodule.span_span_of_tower, f'.span_eq]
  · intro y
    rw [Basis.mem_span_iff_repr_mem]
    constructor
    · intro hy x hx
      rw [← hTspan] at hx
      have hle : Submodule.span O (Set.range bV0) ≤
          Submodule.comap ((m.flip y).restrictScalars O) (1 : Submodule O LL) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        obtain ⟨a, ha⟩ := hy i
        exact Submodule.mem_one.mpr ⟨a, by rw [ha, ← key2, hbV]; rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hle hx)
      exact ⟨a, ha.symm⟩
    · intro hy i
      obtain ⟨a, ha⟩ := hy (bV i) (by rw [hbV, ← hTspan]; exact Submodule.subset_span ⟨i, rfl⟩)
      exact ⟨a, by rw [← key2, ha]⟩
  · intro x
    have hTeq : T = Submodule.span O (Set.range bV) := by
      rw [show (bV : _ → V) = bV0 from funext hbV, hTspan]
    refine (SetLike.ext_iff.mp hTeq x).trans ?_
    rw [Basis.mem_span_iff_repr_mem]
    constructor
    · intro hx y hy
      have hle : Submodule.span O (Set.range f') ≤
          Submodule.comap ((m x).restrictScalars O) (1 : Submodule O LL) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        obtain ⟨a, ha⟩ := hx j
        exact Submodule.mem_one.mpr ⟨a, by rw [ha, ← key1]; rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hle hy)
      exact ⟨a, ha.symm⟩
    · intro hx j
      obtain ⟨a, ha⟩ := hx (f' j) (Submodule.subset_span ⟨j, rfl⟩)
      exact ⟨a, by rw [← key1, ha]⟩

end GlobalTheory.DualLat

namespace GlobalTheory.DualLat

theorem dualLattice_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (LA : Lattice (O := O) A.ρ), IsDual1 (P.PD K) A.ρ A'.ρ m → (∀ g, ∃ a : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL a) → ∃ LA' : Lattice (O := O) A'.ρ, IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m LA hD hc
  obtain ⟨⟨hdom, -, hfr⟩, -⟩ := hO
  obtain ⟨h1, h2, h3, h4⟩ := hD
  obtain ⟨T', hfg, hfree, hspan, hmem1, hmem2⟩ := exists_dual (O := O) m h3 h4 LA.T LA.fg LA.free LA.span
  have hstab : ∀ g, ∀ y ∈ T', (A'.ρ g) y ∈ T' := by
    intro g y hy
    rw [hmem1] at hy ⊢
    intro x hx
    obtain ⟨c, hcg⟩ := hc g
    obtain ⟨a, ha⟩ := hy (A.ρ g⁻¹ x) (LA.stable g⁻¹ x hx)
    refine ⟨c * a, ?_⟩
    have hx' : x = A.ρ g (A.ρ g⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hx', h1, ha, hcg, map_mul]
  let LA' : WeaklyAdmissibleFiltrations.Lattice (O := O) A'.ρ :=
    { T := T', stable := hstab, fg := hfg, free := hfree, span := hspan }
  refine ⟨LA', ⟨⟨h1, h2, h3, h4⟩, hmem1⟩, ⟨⟨?_, ?_, ?_, h4.symm⟩, ?_⟩⟩
  · intro g y x
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  · intro y hy
    exact h3 y (fun x => by simpa only [LinearMap.flip_apply] using hy x)
  · intro x hx
    exact h2 x (fun y => by simpa only [LinearMap.flip_apply] using hx y)
  · intro y
    simpa only [LinearMap.flip_apply] using hmem2 y

end GlobalTheory.DualLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixedMemInvariants
section
namespace GlobalTheory.FixedFinsetInvariants

theorem exists_finset_fixed_mem_invariants {G LL V : Type} [Group G] [Field LL] [AddCommGroup V]
    [Module LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ s : Finset G, ∀ v : V, (∀ g ∈ s, ρ g v = v) → v ∈ Formalism.WeaklyAdmissibleFiltrations.H0V ρ := by
  classical
  let F : Finset G → Submodule LL V := fun s => ⨅ g ∈ s, LinearMap.ker (ρ g - LinearMap.id)
  have hF : ∀ (s : Finset G) (v : V), v ∈ F s ↔ ∀ g ∈ s, ρ g v = v := by
    intro s v
    simp only [F, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule LL V)).has_min (Set.range F) ⟨F ∅, ∅, rfl⟩
  refine ⟨s, fun v hv => ?_⟩
  unfold Formalism.WeaklyAdmissibleFiltrations.H0V
  rw [Submodule.mem_iInf]
  intro g
  have hle : F (insert g s) ≤ F s := by
    intro w hw
    rw [hF] at hw ⊢
    exact fun h hh => hw h (Finset.mem_insert_of_mem hh)
  have heq : F (insert g s) = F s := by
    by_contra hne
    exact hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)
  have hv' : v ∈ F (insert g s) := heq ▸ (hF s v).2 hv
  have hg := (hF _ v).1 hv' g (Finset.mem_insert_self g s)
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact hg

end GlobalTheory.FixedFinsetInvariants
end

