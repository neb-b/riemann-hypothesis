module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShuffle
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MackeyCellTermOfBlockSizes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCohomologySevenElementaryFacts
section
noncomputable section

open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT NumberField IsDedekindDomain ReciprocityTheory.Gal ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory.LocElem

theorem padicInt_coeff {p : ℕ} [Fact p.Prime] : PadicCoeff p ℤ_[p] := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [isAdic_iff]
    have key : ∀ n : ℕ, ((IsLocalRing.maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) := by
      intro n
      ext x
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, SetLike.mem_coe,
        ← PadicInt.norm_le_pow_iff_mem_span_pow, mem_closedBall_zero_iff]
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · rw [key]
      exact IsUltrametricDist.isOpen_closedBall _ (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).ne'
    · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (show (1:ℝ) < p by exact_mod_cast (Fact.out : p.Prime).one_lt))
      refine ⟨n, ?_⟩
      rw [key]
      intro x hx
      apply hball
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      refine lt_of_le_of_lt hx ?_
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact hn
  · rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  · exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem mulSub_open {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (hM : IsFGTop O M) (hO : PadicCoeff p O) {a : O} (ha : a ≠ 0) :
    IsOpen ((mulSub a M : Submodule O M) : Set M) := by
  have := hO.compact
  have := hO.ring
  have := hM.t2
  have := hM.csmul
  obtain ⟨s, hs⟩ := hM.fg.fg_top

  let f : (s → O) →ₗ[O] M := Fintype.linearCombination O (fun i : s => (i : M))
  have hfc : Continuous f := by
    show Continuous fun v : s → O => ∑ i, v i • (i : M)
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hfs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, Subtype.range_coe_subtype,
      Finset.setOfPred_mem, hs]
  have hq : Topology.IsQuotientMap f :=
    (hfc.isClosedMap).isQuotientMap hfc hfs

  have haO : IsOpen ((Ideal.span {a} : Ideal O) : Set O) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have e : (Ideal.span {(u : O) * ϖ ^ n} : Ideal O) = IsLocalRing.maximalIdeal O ^ n := by
      rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
        hϖ.maximalIdeal_eq]
    rw [e]
    exact (isAdic_iff.1 hO.adic).1 n
  have hopen : IsOpen ((((mulSub a M).comap f).toAddSubgroup : AddSubgroup (s → O)) : Set (s → O)) := by
    refine AddSubgroup.isOpen_mono (H₁ := (Submodule.pi Set.univ fun _ => (Ideal.span {a} : Ideal O)).toAddSubgroup) ?_ ?_
    · intro v hv
      have : ∀ i, ∃ w : O, a * w = v i := fun i => by
        obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hv i (Set.mem_univ i))
        exact ⟨w, by rw [mul_comm]; exact hw⟩
      choose w hw using this
      refine ⟨f w, ?_⟩
      show a • f w = f v
      rw [← map_smul]
      congr 1
      funext i
      exact hw i
    · show IsOpen (Set.univ.pi fun _ => ((Ideal.span {a} : Ideal O) : Set O))
      exact isOpen_set_pi Set.finite_univ fun _ _ => haO
  rw [← hq.isOpen_preimage]
  exact hopen

theorem contAction_quotient {O G V : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup V] [Module O V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] {ρ : Representation O G V} (h : ReciprocityTheory.Gal.ContAction ρ)
    (T : Submodule O V) (hT : StableUnder ρ T) : ReciprocityTheory.Gal.ContAction (ρ.quotient T hT) := by
  have hq : IsOpenQuotientMap (Prod.map (id : G → G) T.mkQ) :=
    IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ T)
  unfold ReciprocityTheory.Gal.ContAction
  rw [hq.isQuotientMap.continuous_iff]
  exact continuous_quot_mk.comp h

theorem cup_eq_zero_of_coboundary {O : Type} [CommRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {M T₂ P : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul O M] [AddCommGroup T₂] [Module O T₂] [TopologicalSpace T₂]
    [IsTopologicalAddGroup T₂] [ContinuousConstSMul O T₂] [AddCommGroup P] [Module O P]
    [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul O P]
    (ρM : Representation O Γ M) (ρ₂ : Representation O Γ T₂) (ρP : Representation O Γ P)
    (b : M →ₗ[O] T₂ →ₗ[O] P) (hb : Continuous fun q : M × T₂ => b q.1 q.2)
    (hbe : ∀ g x y, b (ρM g x) (ρ₂ g y) = ρP g (b x y)) (h₂ : ReciprocityTheory.Gal.ContAction ρ₂)
    (x : Z1 ρM) (t : Z1 ρ₂) (c : Γ → P) (hc : Continuous c)
    (hcz : ∀ g h, b (ρM g (x.1 h)) (t.1 g) = ρP g (c h) - c (g * h) + c g) :
    cupProductH1H1 ρM ρ₂ ρP b hb hbe h₂ (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0 := by
  show (Submodule.Quotient.mk (cupCocycleZ1Z1 ρM ρ₂ ρP b hb hbe h₂ x t) : H2 ρP) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -(b (x.1 g) (t.1 g)) - c g, ((hb.comp (x.2.1.prodMk t.2.1)).neg).sub hc, ?_⟩
  funext q
  obtain ⟨g, h⟩ := q
  have e := hcz g h
  simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, map_sub, map_neg, ← hbe, x.2.2 g h, t.2.2 g h, map_add (f := _),
    LinearMap.add_apply]
  have e' : ρP g (c h) = b (ρM g (x.1 h)) (t.1 g) + c (g * h) - c g := by rw [e]; abel
  rw [e']
  abel

theorem pr_eq_zero_of_coboundary {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (x : Z1 D.ρA) (t : Z1 D.ρTl') (c : G → KO O) (hc : Continuous c)
    (hcz : ∀ g k, pairKO D.bT D.T (D.ρA g (x.1 k)) (t.1 g) = ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) :
    D.pr (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0 := by
  show D.inv (cupProductH1H1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T)
    D.pairKO_equiv (sub_contAction D.contT' _ D.stT') (Submodule.Quotient.mk x) (Submodule.Quotient.mk t)) = 0
  have h0 := cup_eq_zero_of_coboundary D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T)
    D.pairKO_equiv (sub_contAction D.contT' _ D.stT') x t c hc (fun g k => hcz g k)
  exact (congrArg D.inv h0).trans (map_zero _)

theorem quotShape_of_equiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [AddCommGroup X]
    [Module O X] (Hc F Hc' F' : Submodule O X) (d : ℕ)
    (e : (Hc ⧸ F.comap Hc.subtype) ≃ₗ[O] (Hc' ⧸ F'.comap Hc'.subtype)) (h : QuotShape Hc F d) :
    QuotShape Hc' F' d := by
  obtain ⟨Cy, i1, i2, ι, π, hι, hex, c0, hc0⟩ := h
  refine ⟨Cy, i1, i2, e.toLinearMap ∘ₗ ι, π ∘ₗ e.symm.toLinearMap, e.injective.comp hι, ?_, c0, hc0⟩
  intro y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_range]
  rw [hex (e.symm y)]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z, by rw [hz, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨z, hz⟩; exact ⟨z, by rw [← hz, LinearEquiv.symm_apply_apply]⟩

theorem mem_integers_iff_norm_le_one {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 :=
  GlobalTheory.EmbInj.mem_OL_iff LL x

theorem isOpen_integers {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) :
    IsOpen (Set.range (algebraMap ↥(Formalism.BasicNotions.Loc.OL LL) ↥LL.1)) :=
  (GlobalTheory.LitGood.litGoodO l LL).2.2.2.2

theorem elem : ReciprocityTheory.ChartRestriction.T2.Elem :=
  ⟨@padicInt_coeff, @mulSub_open, @contAction_quotient, @pr_eq_zero_of_coboundary,
    @quotShape_of_equiv, @mem_integers_iff_norm_le_one, @isOpen_integers⟩

end GlobalTheory.LocElem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLCoeffMapFunctorial
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelFun

section General

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho : Representation R Γ M) (rho' : Representation R Γ M') (u : M →ₗ[R] M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

theorem selMaps_res_map {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (mapH1 rho rho' u hu he x) =
      mapH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem selMaps_map_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    mapH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (selMaps_res_map rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
  {B B' : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
  [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']

theorem localConditionAboveL_coeffMap_functorial (f : B →ₗ[Λ] B') (v : PlE D.host) (x : H1 ((repOn ρ κ B).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ B v) : h1MapSubgroup ρ κ (DecV N v) f x ∈ bkOn bkP i ρ κ B' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨cocycles1MapOfEquivariant _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology
        (fun g m => repOn_map ρ κ f g.1 m) z, c, y, f b, hc, hy, fun g a => ?_, rfl⟩
      change f ((z : ↥(DecV N v) → Fin r → B) g a) = _
      rw [hz, map_smul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem selmerClass_coeffMap_mem_selmer (f : B →ₗ[Λ] B') (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ B))
    (hx : x ∈ selOn bkP i ρ κ B Q) : h1Map ρ κ f x ∈ selOn bkP i ρ κ B' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (selMaps_res_map (repOn ρ κ B) (repOn ρ κ B') (f.compLeft (Fin r)) continuous_of_discreteTopology
    (repOn_map ρ κ f) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact localConditionAboveL_coeffMap_functorial bkP i ρ κ f v _ hv
  · exact Submodule.mem_top
  · exact selMaps_map_ur _ _ _ _ _ _ _ hv

theorem selMaps (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)) : SelMaps bkP i s κ Q := by
  intro B B' _ _ _ _ _ _ _ _ f
  rintro _ ⟨x, hx, rfl⟩
  exact selmerClass_coeffMap_mem_selmer bkP i _ κ f Q x hx

end GlobalTheory.SelFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDegreeSum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.Proof.LocalDegreeSum

theorem sum_locDeg : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] [Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}], ∑ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, ReciprocityTheory.Gal.locDeg v.1 = Module.finrank ℚ F := by
  intro F _ _ l hl _
  classical

  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hp
  have hpmax : p.IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have : p.IsPrime := hpmax.isPrime
  have hp0 : p ≠ 0 := by
    rw [hp, Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.out.ne_zero

  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      ((l : ℕ) : 𝓞 F) ∈ v.asIdeal ↔ v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 F)) p := by
    intro v
    rw [Ideal.dvd_iff_le, hp, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem]
    simp

  let e := (Equiv.subtypeEquivRight key).trans (HeightOneSpectrum.equivPrimesOver (𝓞 F) hp0)
  rw [← NumberField.RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)]
  exact Fintype.sum_equiv e _ _ (fun v => by rfl)

end GlobalTheory.Proof.LocalDegreeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MackeyFormulaHarishChandraRestrictionInduction
section
noncomputable section

namespace GlobalTheory.GLq.Mackey

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem blocks_conj (a b n : ℕ) (hn : n = a + b) (P : Subgroup (Gn g n))
    (hP : ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) (Λ : Gn g a → Gn g b → ℂ)
    (h1 : ∀ y, IsClass fun x => Λ x y) (h2 : ∀ x, IsClass (Λ x)) :
    ∀ h ∈ P, ∀ x ∈ P, Λ (toG (tl a ((h * x * h⁻¹ : Gn g n) : Mt g n))) (toG (br a b ((h * x * h⁻¹ : Gn g n) : Mt g n)))
      = Λ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) := by
  obtain ⟨-, -, hu, hmul, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn
  let f₁ : P →* Gn g a := MonoidHom.mk' (fun p => toG (tl a ((p : Gn g n) : Mt g n))) (by
    intro p q
    have hp : InPar a ((p : Gn g n) : Mt g n) := (hP p).1 p.2
    have hq : InPar a ((q : Gn g n) : Mt g n) := (hP q).1 q.2
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (hmul _ _ hp hq).1, Units.val_mul,
      Recip.coe_toG ((hu _ hp).1.mul (hu _ hq).1), Recip.coe_toG (hu _ hp).1, Recip.coe_toG (hu _ hq).1])
  let f₂ : P →* Gn g b := MonoidHom.mk' (fun p => toG (br a b ((p : Gn g n) : Mt g n))) (by
    intro p q
    have hp : InPar a ((p : Gn g n) : Mt g n) := (hP p).1 p.2
    have hq : InPar a ((q : Gn g n) : Mt g n) := (hP q).1 q.2
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (hmul _ _ hp hq).2, Units.val_mul,
      Recip.coe_toG ((hu _ hp).2.mul (hu _ hq).2), Recip.coe_toG (hu _ hp).2, Recip.coe_toG (hu _ hq).2])
  intro h hh x hx
  have E1 : toG (tl a ((h * x * h⁻¹ : Gn g n) : Mt g n)) = f₁ ⟨h, hh⟩ * f₁ ⟨x, hx⟩ * (f₁ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  have E2 : toG (br a b ((h * x * h⁻¹ : Gn g n) : Mt g n)) = f₂ ⟨h, hh⟩ * f₂ ⟨x, hx⟩ * (f₂ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  rw [E1, E2]
  exact (h2 _ _ _).trans (h1 _ _ _)

theorem mean_prod_right {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun p : A × B => F p.1 p.2) = mean (fun b => mean (fun a => F a b)) := by
  unfold mean
  rw [Fintype.sum_prod_type_right, Fintype.card_prod]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  push_cast; rw [mul_inv]; ring

theorem mean_prod_left {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun p : A × B => F p.1 p.2) = mean (fun a => mean (fun b => F a b)) := by
  unfold mean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  push_cast; rw [mul_inv]; ring

theorem mean_swap {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun b => mean (fun a => F a b)) = mean (fun a => mean (fun b => F a b)) := by
  rw [← mean_prod_right, mean_prod_left]

theorem mean_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (F : B → ℂ) :
    mean (fun x => F (e x)) = mean F := by
  unfold mean
  rw [Fintype.card_congr e, Equiv.sum_comp e F]

theorem mean_sum {A ι : Type} [Fintype A] (R : Finset ι) (Λ : A → ℂ) (T : ι → A → ℂ) :
    mean (fun p => Λ p * ∑ i ∈ R, T i p) = ∑ i ∈ R, mean (fun p => Λ p * T i p) := by
  unfold mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem res_comm {p q r s m k : ℕ} (Λ : Gn g m → Gn g k → ℂ) (y₁ : Gn g p) (y₃ : Gn g q) (y₂ : Gn g r)
    (y₄ : Gn g s) :
    res r s (fun h₂ => res p q (fun x => Λ x h₂) y₁ y₃) y₂ y₄ =
      res p q (fun z => res r s (Λ z) y₂ y₄) y₁ y₃ := by
  unfold res
  simp only [← Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  ring

theorem left_side (a b c d n : ℕ) (hn1 : n = a + b) (hn2 : n = c + d) (Φ : Gn g a → Gn g b → ℂ)
    (hΦ1 : ∀ y, IsClass fun x => Φ x y) (hΦ2 : ∀ x, IsClass (Φ x))
    (Λ : Gn g c → Gn g d → ℂ) (hΛ1 : ∀ y, IsClass fun x => Λ x y) (hΛ2 : ∀ x, IsClass (Λ x)) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d (hcT a b Φ n) p.1 p.2) =
      ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        mean (fun y : (Gn g i × Gn g (a - i)) × (Gn g (c - i) × Gn g (b - (c - i))) =>
          res i (c - i) (fun z => res (a - i) (b - (c - i)) (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  obtain ⟨-, R2, -⟩ := Recip.reciprocity g
  obtain ⟨⟨Pc, hPc⟩, -, -, -, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g c d n hn2
  obtain ⟨⟨Pa, hPa⟩, -, -, -, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn1
  have hR : ∀ x : Gn g n, ∃! i, i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧
      ∃ h ∈ Pc, ∃ k ∈ Pa, x = h * wI g a c i n * k := by
    intro x
    obtain ⟨i, ⟨hi, p, q, hp, hq, e⟩, hu⟩ := GlobalTheory.GLm.ParCoset.doubleCoset g a b c d n hn1 hn2 x
    refine ⟨i, ⟨hi, p, (hPc p).2 hp, q, (hPa q).2 hq, e⟩, ?_⟩
    rintro j ⟨hj, h, hh, k, hk, e'⟩
    exact hu j ⟨hj, h, k, (hPc h).1 hh, (hPa k).1 hk, e'⟩
  have hm := mackey_doubleCoset_pairing (Gn g n) Pc Pa ℕ
    ((Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b)) (fun i => wI g a c i n) hR
    (fun x => Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))))
    (fun z => Φ (toG (tl a (z : Mt g n))) (toG (br a b (z : Mt g n))))
    (blocks_conj c d n hn2 Pc hPc Λ hΛ1 hΛ2) (blocks_conj a b n hn1 Pa hPa Φ hΦ1 hΦ2)
  have cc : ∀ (P : Subgroup (Gn g n)) (Q : Gn g n → Prop), (∀ x, x ∈ P ↔ Q x) →
      Nat.card P = (Finset.univ.filter Q).card := by
    intro P Q hP
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [hP]
  rw [cc Pc _ hPc, cc Pa _ hPa] at hm
  simp only [hPc, hPa] at hm
  rw [R2 c d n hn2]
  unfold hcT
  rw [hm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  exact mackey_cell_term g a b c d n i hn1 hn2 (by omega) hi.2.1 hi.2.2 Λ Φ

theorem right_term (a b c d n i : ℕ) (hn1 : n = a + b) (hn2 : n = c + d) (hia : i ≤ a) (hic : i ≤ c)
    (hcb : c - i ≤ b) (Φ : Gn g a → Gn g b → ℂ) (Λ : Gn g c → Gn g d → ℂ)
    (hΛ1 : ∀ y, IsClass fun x => Λ x y) (hΛ2 : ∀ x, IsClass (Λ x)) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i))
      (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d p.2) c p.1) =
    mean (fun y : (Gn g i × Gn g (a - i)) × (Gn g (c - i) × Gn g (b - (c - i))) =>
      res i (c - i) (fun z => res (a - i) (b - (c - i)) (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 *
        res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  have hc : c = i + (c - i) := by omega
  have hd : d = (a - i) + (b - (c - i)) := by omega
  obtain ⟨R1, -, -⟩ := Recip.reciprocity g
  rw [mean_prod_right (fun (h₁ : Gn g c) (h₂ : Gn g d) => Λ h₁ h₂ * hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i))
      (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁)]
  calc _ = mean (fun h₂ : Gn g d => mean (fun q : Gn g i × Gn g (c - i) =>
          res i (c - i) (fun x => Λ x h₂) q.1 q.2 * hcT (a - i) (b - (c - i))
            (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 y₄) q.1 y₂) d h₂)) := by
        congr 1; funext h₂
        exact R1 i (c - i) c hc (fun x => Λ x h₂) _ (hΛ1 h₂)
    _ = mean (fun q : Gn g i × Gn g (c - i) => mean (fun h₂ : Gn g d =>
          res i (c - i) (fun x => Λ x h₂) q.1 q.2 * hcT (a - i) (b - (c - i))
            (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 y₄) q.1 y₂) d h₂)) :=
        mean_swap _
    _ = mean (fun q : Gn g i × Gn g (c - i) => mean (fun r : Gn g (a - i) × Gn g (b - (c - i)) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) q.1 q.2) r.1 r.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 r.2) q.1 r.1)) := by
        congr 1; funext q
        refine R1 (a - i) (b - (c - i)) d hd _ _ ?_
        intro x y
        show res i (c - i) (fun z => Λ z (y * x * y⁻¹)) q.1 q.2 = res i (c - i) (fun z => Λ z x) q.1 q.2
        rw [show (fun z => Λ z (y * x * y⁻¹)) = (fun z => Λ z x) from funext fun z => hΛ2 z x y]
    _ = mean (fun w : (Gn g i × Gn g (c - i)) × (Gn g (a - i) × Gn g (b - (c - i))) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) w.1.1 w.1.2) w.2.1 w.2.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) w.1.2 w.2.2) w.1.1 w.2.1) :=
        (mean_prod_left (fun (q : Gn g i × Gn g (c - i)) (r : Gn g (a - i) × Gn g (b - (c - i))) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) q.1 q.2) r.1 r.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 r.2) q.1 r.1)).symm
    _ = _ := by
        rw [← mean_equiv (Equiv.prodProdProdComm (Gn g i) (Gn g (a - i)) (Gn g (c - i)) (Gn g (b - (c - i))))]
        congr 1; funext y
        simp only [Equiv.prodProdProdComm_apply]
        rw [res_comm]

theorem mackey_formula : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d →
    ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → ∀ h₁ h₂,
      res c d (hcT a b Φ n) h₁ h₂ = ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ =>
          res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁ := by
  intro g _ a b c d n hn1 hn2 Φ hΦ1 hΦ2 h₁ h₂
  obtain ⟨-, -, R3⟩ := Recip.reciprocity g
  have hcl : IsClass (hcT a b Φ n) := (_root_.GlobalTheory.GLq.HcClass.hc_class g a b n hn1).1 Φ
  have hres := (_root_.GlobalTheory.GLq.HcClass.hc_class g c d n hn2).2 _ hcl
  suffices H : (fun (h₁ : Gn g c) (h₂ : Gn g d) => res c d (hcT a b Φ n) h₁ h₂) =
      (fun (h₁ : Gn g c) (h₂ : Gn g d) => ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ =>
          res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁) from
    congrFun (congrFun H h₁) h₂
  refine R3 (Gn g c) (Gn g d) _ _ hres.2 hres.1 ?_ ?_ ?_
  · intro y x z
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact (_root_.GlobalTheory.GLq.HcClass.hc_class g i (c - i) c (by omega)).1 _ x z
  · intro x y z
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hd' : ∀ Ψ, hcT (a - i) (b - (c - i)) Ψ d (z * y * z⁻¹) = hcT (a - i) (b - (c - i)) Ψ d y :=
      fun Ψ => (_root_.GlobalTheory.GLq.HcClass.hc_class g (a - i) (b - (c - i)) d (by omega)).1 Ψ y z
    simp only [hd']
  · intro Λ hΛ1 hΛ2
    rw [left_side a b c d n hn1 hn2 Φ hΦ1 hΦ2 Λ hΛ1 hΛ2, mean_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact (right_term a b c d n i hn1 hn2 (by omega) hi.2.1 hi.2.2 Φ Λ hΛ1 hΛ2).symm

end GlobalTheory.GLq.Mackey
end
end

