module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuedEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

section General

theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx

variable {L : Type} [Field L] [NumberField L]


open scoped WithZeroTopology in
theorem exists_finCompl_map (c : L ≃+* L) {v v' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c v v') :
    ∃ φ : v.adicCompletion L →+* v'.adicCompletion L, Continuous φ ∧
      (∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k)) ∧ ∀ x, Valued.v (φ x) = Valued.v x := by
  have hc : Continuous (WithVal.map (v.valuation L) (v'.valuation L) (c : L →+* L)) :=
    continuous_of_valued_eq (fun γ => by
      obtain ⟨k, hk⟩ := v.valuation_surjective L γ
      exact ⟨WithVal.toVal _ k, hk⟩) _ fun x => h x.ofVal
  let φ : v.adicCompletion L →+* v'.adicCompletion L :=
    ((HeightOneSpectrum.adicCompletion.equiv L v').symm.toRingHom.comp
      (UniformSpace.Completion.mapRingHom _ hc)).comp (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom
  have h1 : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L v').comp
      (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))
  have h2 : ∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k) := fun k => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ k)
  refine ⟨φ, h1, h2, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap L v).induction_on (p := fun x => Valued.v (φ x) = Valued.v x) x
    (isClosed_eq ((Valued.continuous_valuation_of_surjective (v'.valuedAdicCompletion_surjective L)).comp h1)
      (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective L))) fun k => ?_
  rw [h2]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v' _).trans
    ((h k).trans (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm)


omit [NumberField L] in
theorem exists_infCompl_map (c : L ≃+* L) (w : InfinitePlace L) :
    ∃ φ : (w.comap (c : L →+* L)).Completion →+* w.Completion, Continuous φ ∧
      ∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k) := by
  have hc : Continuous (WithAbs.map (w.comap (c : L →+* L)).1 w.1 (c : L →+* L)) :=
    (AddMonoidHomClass.isometry_of_norm _ fun x => rfl).continuous
  let φ : (w.comap (c : L →+* L)).Completion →+* w.Completion :=
    ((AbsoluteValue.Completion.ofCompletion (v := w.1)).comp
      (UniformSpace.Completion.mapRingHom _ hc)).comp
        (AbsoluteValue.Completion.toCompletion (v := (w.comap (c : L →+* L)).1))
  have hφ : Continuous φ :=
    (AbsoluteValue.Completion.continuous_ofCompletion w.1).comp
      (UniformSpace.Completion.continuous_map.comp
        (AbsoluteValue.Completion.continuous_toCompletion _))
  refine ⟨φ, hφ, fun k => ?_⟩
  apply AbsoluteValue.Completion.toCompletion_injective w.1
  simpa [φ, AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply] using
    (UniformSpace.Completion.mapRingHom_coe hc (WithAbs.toAbs _ k))

theorem conjPl_symm_iff (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) : ConjPl c.symm v' v ↔ ConjPl c v v' :=
  ⟨fun h x => by simpa using (h (c x)).symm, fun h x => by simpa using (h (c.symm x)).symm⟩

theorem map_update_one {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, Ring (M i)] {f : ι → ι}
    (hf : Function.Injective f) (φ : ∀ j, M (f j) →+* M j) (j : ι) (x : M (f j)) :
    (fun i => φ i (Function.update (fun i => (1 : M i)) (f j) x (f i))) =
      Function.update (fun i => (1 : M i)) j (φ j x) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · rw [Function.update_of_ne hi, Function.update_of_ne (hf.ne hi), map_one]

end General


open Classical in
theorem exists_isConjI : ∀ (L : Type) [Field L] [NumberField L] (c : L ≃+* L), ∃ C : Ideles L →* Ideles L, IsConjI c C := by
  intro L _ _ c
  choose f hf hfu using fun v => existsUnique_conjPl c.symm v
  have hf' : ∀ v, ConjPl c (f v) v := fun v => (conjPl_symm_iff c _ _).1 (hf v)
  have hfe : ∀ {v v'}, ConjPl c v v' → v = f v' := fun h => hfu _ _ ((conjPl_symm_iff c _ _).2 h)
  have hfi : Function.Injective f := fun a b hab =>
    (existsUnique_conjPl c (f a)).unique (hf' a) (hab ▸ hf' b)
  choose φ φc φk φv using fun v => exists_finCompl_map c (hf' v)
  choose ψ ψc ψk using exists_infCompl_map c
  have hg : ∀ w : InfinitePlace L, (w.comap (c.symm : L →+* L)).comap (c : L →+* L) = w := fun w => by
    ext x
    simp
  have hgi : Function.Injective fun w : InfinitePlace L => w.comap (c : L →+* L) := fun a b hab => by
    ext x
    simpa using congrArg (fun w : InfinitePlace L => w (c.symm x)) hab
  have hφ : ∀ᶠ j in Filter.cofinite, Set.MapsTo (φ j) ((f j).adicCompletionIntegers L) (j.adicCompletionIntegers L) :=
    Filter.Eventually.of_forall fun j x hx => (φv j x).trans_le hx
  let Φ : FiniteAdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L :=
    RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) f hfi.tendsto_cofinite φ hφ
  have Φc : Continuous Φ :=
    RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) f hfi.tendsto_cofinite (fun j r => φ j r) hφ φc
  let Ψ : InfiniteAdeleRing L →+* InfiniteAdeleRing L :=
    RingHom.pi fun w => (ψ w).comp (Pi.evalRingHom (fun w : InfinitePlace L => w.Completion) (w.comap (c : L →+* L)))
  have Ψc : Continuous Ψ := continuous_pi fun w => (ψc w).comp (continuous_apply _)
  let A : AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L := RingHom.prodMap Ψ Φ
  have Ac : Continuous A := Ψc.prodMap Φc
  let C : Ideles L →* Ideles L := Units.map A.toMonoidHom
  have hinf : ∀ (w w' : InfinitePlace L) (e : w'.comap (c : L →+* L) = w), ∃ θ : w.Completion →+* w'.Completion,
      (∀ k : L, θ (algebraMap L _ k) = algebraMap L _ (c k)) ∧
      ∀ y, C (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w y) =
        ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w' (Units.map θ.toMonoidHom y) := by
    rintro _ w' rfl
    exact ⟨ψ w', ψk w', fun y => Units.ext (Prod.ext (map_update_one hgi ψ w' y) (map_one Φ))⟩
  have hloc : ∀ v (y : ((f v).adicCompletion L)ˣ),
      C (Neutral.B1.localIdele L (f v) y) = Neutral.B1.localIdele L v (Units.map (φ v).toMonoidHom y) := fun v y =>
    Units.ext (Prod.ext (map_one Ψ) (Subtype.ext (map_update_one hfi φ v y)))
  refine ⟨C, Continuous.units_map _ Ac, fun k => ?_, fun w k => ?_, fun w y => ?_, fun v v' h k => ?_,
    fun v v' h x => ?_, fun v v' h a => ?_⟩
  · exact Units.ext (Prod.ext (funext fun w => ψk w k) (FiniteAdeleRing.ext _ fun v => φk v k))
  · obtain ⟨θ, h1, h2⟩ := hinf w _ (hg w)
    rw [h2]
    exact congrArg _ (Units.ext (h1 k))
  · obtain ⟨θ, -, h2⟩ := hinf w _ (hg w)
    exact ⟨_, h2 y⟩
  · obtain rfl := hfe h
    rw [hloc]
    exact congrArg _ (Units.ext (φk v' k))
  · obtain rfl := hfe h
    exact ⟨_, hloc v' x⟩
  · obtain rfl := hfe h
    refine ⟨φv v' _, ?_⟩
    rw [← φv v' (_ - 1), map_sub (φ v'), map_one (φ v')]
    rfl

end GlobalTheory.Mem.Chr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Filter Topology

namespace GlobalTheory.FrobDense

variable {E : Type} [Field E] [NumberField E]

def abv (S : Finset (HeightOneSpectrum (𝓞 E))) : S ⊕ InfinitePlace E → AbsoluteValue E ℝ
  | Sum.inl v => GlobalTheory.LocalQuad.Approx.abv S (Sum.inl v)
  | Sum.inr w => w.1

theorem abv_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 E))) (i : S ⊕ InfinitePlace E) :
    (abv S i).IsNontrivial := by
  rcases i with v | w
  · exact GlobalTheory.LocalQuad.Approx.abv_isNontrivial S (Sum.inl v)
  · exact InfinitePlace.isNontrivial _

theorem abv_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 E))) (v : S) (w : InfinitePlace E) :
    ¬ (abv S (Sum.inl v)).IsEquiv (abv S (Sum.inr w)) := by
  intro h
  have h1 : abv S (Sum.inl v) ((2 : ℕ) : E) ≤ 1 :=
    NumberField.HeightOneSpectrum.adicAbv_natCast_le_one E v.1 2
  rw [h.le_one_iff] at h1
  have h2 : abv S (Sum.inr w) ((2 : ℕ) : E) = 2 := by
    show w ((2 : ℕ) : E) = 2
    rw [← w.norm_embedding_eq, map_natCast]
    simp
  rw [h2] at h1
  norm_num at h1

theorem abv_pairwise (S : Finset (HeightOneSpectrum (𝓞 E))) :
    Pairwise fun i j ↦ ¬(abv S i).IsEquiv (abv S j) := by
  rintro (v | σ) (w | τ) hne h
  · exact GlobalTheory.LocalQuad.Approx.abv_pairwise S (i := Sum.inl v) (j := Sum.inl w)
      (fun e => hne (congrArg Sum.inl (Sum.inl_injective e))) h
  · exact abv_not_isEquiv S v τ h
  · exact abv_not_isEquiv S w σ h.symm
  · exact hne (congrArg Sum.inr (InfinitePlace.eq_iff_isEquiv.2 h))

abbrev Loc (S : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  ((w : InfinitePlace E) → w.Completion) × ((v : S) → v.1.adicCompletion E)

def proj (S : Finset (HeightOneSpectrum (𝓞 E))) : AdeleRing (𝓞 E) E →* Loc S where
  toFun a := (fun w => a.1 w, fun v => a.2 v.1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem denseRange_inf (w : InfinitePlace E) : DenseRange (algebraMap E w.Completion) := by
  refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
  rintro _ ⟨a, rfl⟩
  refine ⟨WithAbs.equiv w.1 a, ?_⟩
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  simp

theorem norm_inf (w : InfinitePlace E) (x : E) : ‖algebraMap E w.Completion x‖ = w x := by
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  simpa using InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm x)

theorem denseRange_proj (S : Finset (HeightOneSpectrum (𝓞 E))) :
    DenseRange fun x : E => proj S (algebraMap E (AdeleRing (𝓞 E) E) x) := by
  refine Metric.denseRange_iff.2 fun y ε hε => ?_
  have hε2 : 0 < ε / 2 := half_pos hε
  choose a ha using fun v : S =>
    Metric.denseRange_iff.1 (HeightOneSpectrum.denseRange_algebraMap E v.1) (y.2 v) _ hε2
  choose b hb using fun w : InfinitePlace E =>
    Metric.denseRange_iff.1 (denseRange_inf w) (y.1 w) _ hε2
  obtain ⟨x, hx⟩ := GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt (abv_isNontrivial S) (abv_pairwise S)
    (Sum.elim a b) hε2
  refine ⟨x, ?_⟩
  rw [Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hε, dist_pi_lt_iff hε]
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have h1 : w (b w - x) < ε / 2 := hx (Sum.inr w)
    rw [← norm_inf, map_sub, ← dist_eq_norm] at h1
    have h2 := dist_triangle (y.1 w) (algebraMap E _ (b w)) (algebraMap E _ x)
    have h3 := hb w
    change dist (y.1 w) (algebraMap E _ x) < ε
    linarith
  · have h1 : GlobalTheory.LocalQuad.Approx.abv S (Sum.inl v) (a v - x) < ε / 2 := hx (Sum.inl v)
    rw [GlobalTheory.LocalQuad.Approx.abv_inl, map_sub, ← dist_eq_norm] at h1
    have h2 := dist_triangle (y.2 v) (algebraMap E _ (a v)) (algebraMap E _ x)
    have h3 := ha v
    change dist (y.2 v) (algebraMap E _ x) < ε
    linarith

theorem denseRange_units (S : Finset (HeightOneSpectrum (𝓞 E))) :
    DenseRange fun k : Eˣ => Units.map (proj S) (diagUnits E k) := by
  have hg : IsOpenEmbedding (Units.val : (Loc S)ˣ → Loc S) := Units.isOpenEmbedding_val
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (denseRange_proj S).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact left_ne_zero_of_mul_eq_one (congrArg (fun y : Loc S => y.1 w) v.mul_inv)
      (congrArg (fun y : Loc S => y.1 w) hk)
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

def incl (S : Finset (HeightOneSpectrum (𝓞 E))) : Loc S →* AdeleRing (𝓞 E) E :=
  MonoidHom.prodMap (MonoidHom.id (InfiniteAdeleRing E))
    (∏ v : S, (Neutral.B1.finiteSingle E v.1).comp (Pi.evalMonoidHom (fun v : S => v.1.adicCompletion E) v))

theorem incl_snd (S : Finset (HeightOneSpectrum (𝓞 E))) (y : Loc S) :
    (incl S y).2 = ∏ v : S, Neutral.B1.finiteSingle E v.1 (y.2 v) :=
  MonoidHom.finsetProd_apply _ _ _

theorem continuous_incl (S : Finset (HeightOneSpectrum (𝓞 E))) : Continuous (incl S) := by
  refine Continuous.prodMk continuous_fst (?_ : Continuous fun y => (incl S y).2)
  simp only [incl_snd]
  exact continuous_finsetProd _ fun v _ =>
    (GlobalTheory.Mem.UnrAe.continuous_finSingle v.1).comp ((continuous_apply v).comp continuous_snd)

theorem incl_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (y : Loc S) (v : S) : (incl S y).2 v.1 = y.2 v := by
  classical
  let e : FiniteAdeleRing (𝓞 E) E →* v.1.adicCompletion E :=
    (GlobalTheory.Mem.LocTriv.ev v.1).comp (MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  show e (incl S y).2 = _
  rw [incl_snd, map_prod, Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
  · exact Function.update_self v.1 (y.2 v) (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))
  · intro w _ hw
    exact Function.update_of_ne (fun h => hw (Subtype.ext h.symm)) (y.2 w)
      (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))

theorem proj_incl (S : Finset (HeightOneSpectrum (𝓞 E))) (y : Loc S) : proj S (incl S y) = y :=
  Prod.ext rfl (funext fun v => incl_apply S y v)

variable {B : Type} [CommGroup B] [TopologicalSpace B] [T2Space B]


open GlobalTheory.Mem.LocTriv GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.IdlFact in
theorem eq_one_of_local (ψ : GlobalTheory.Mem.Chr.Ideles E →* B) (hψ : Continuous ψ)
    (a : GlobalTheory.Mem.Chr.Ideles E)
    (h1 : (a : AdeleRing (𝓞 E) E).1 = 1) (hl : ∀ v, ψ (GlobalTheory.Mem.Chr.localIdele E v (Units.map (ev v) a)) = 1) : ψ a = 1 := by
  have hp : ∀ (c : GlobalTheory.Mem.Chr.Ideles E) T, (∀ v, ψ (GlobalTheory.Mem.Chr.localIdele E v (Units.map (ev v) c)) = 1) → ψ (part c T) = 1 :=
    fun c T hc => by
      rw [part, map_prod]
      exact Finset.prod_eq_one fun v _ => hc v
  let T := (finite_valAt_ne_one a).toFinset
  let b := part a⁻¹ T * a
  have hb1 : ∀ v ∈ T, ev v (b : AdeleRing (𝓞 E) E) = 1 := fun v hv => by
    simp only [b]
    rw [Units.val_mul, map_mul, ev_part_mem _ hv, ← map_mul, Units.inv_mul, map_one]
  have hb2 : ∀ v ∉ T, ev v (b : AdeleRing (𝓞 E) E) = ev v (a : AdeleRing (𝓞 E) E) := fun v hv => by
    simp only [b]
    rw [Units.val_mul, map_mul, ev_part_not_mem _ hv, one_mul]
  have hbu : b ∈ unitIdl E := fun v => by
    show Valued.v (ev v (b : AdeleRing (𝓞 E) E)) = 1
    by_cases hv : v ∈ T
    · rw [hb1 v hv, map_one]
    · rw [hb2 v hv]
      have h : valAt v a = 1 := by simpa [T] using hv
      exact h
  have hbi : (b : AdeleRing (𝓞 E) E).1 = 1 := by
    show (part a⁻¹ T : AdeleRing (𝓞 E) E).1 * (a : AdeleRing (𝓞 E) E).1 = 1
    rw [part_fst, h1, one_mul]
  have hbl : ∀ v, ψ (GlobalTheory.Mem.Chr.localIdele E v (Units.map (ev v) b)) = 1 := fun v => by
    by_cases hv : v ∈ T
    · rw [show Units.map (ev v) b = 1 from Units.ext (hb1 v hv), map_one, map_one]
    · rw [show Units.map (ev v) b = Units.map (ev v) a from Units.ext (hb2 v hv), hl]
  have t := (hψ.tendsto b).comp (tendsto_part hbu fun w => congrFun hbi w)
  rw [show ψ ∘ part b = fun _ => 1 from funext fun S => hp b S hbl] at t
  have hb : ψ b = 1 := tendsto_nhds_unique t tendsto_const_nhds
  simp only [b] at hb
  rwa [← part_inv, map_mul, map_inv, hp a T hl, inv_one, one_mul] at hb


open GlobalTheory.Mem.LocTriv in
theorem eq_one_of_away (ψ : Ideles E →* B) (hψ : Continuous ψ) (hd : ∀ k, ψ (diagUnits E k) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ v ∉ S, ∀ x, ψ (localIdele E v x) = 1) : ψ = 1 := by
  have h0 : ∀ a : Ideles E, Units.map (proj S) a = 1 → ψ a = 1 := fun a ha => by
    have e : proj S (a : AdeleRing (𝓞 E) E) = 1 := congrArg Units.val ha
    refine eq_one_of_local ψ hψ a (congrArg Prod.fst e) fun v => ?_
    by_cases hv : v ∈ S
    · rw [show Units.map (ev v) a = 1 from Units.ext (congrFun (congrArg Prod.snd e) ⟨v, hv⟩), map_one, map_one]
    · exact hS v hv _
  have h1 : ∀ a : Ideles E, ψ (Units.map (incl S) (Units.map (proj S) a)) = ψ a := fun a => by
    rw [← div_eq_one, ← map_div]
    refine h0 _ ?_
    rw [map_div, div_eq_one]
    exact Units.ext (proj_incl S _)
  have h2 : ∀ y, ψ (Units.map (incl S) y) = 1 := fun y =>
    (denseRange_units S).induction_on (p := fun y => ψ (Units.map (incl S) y) = 1) y
      (isClosed_eq (hψ.comp ((continuous_incl S).units_map _)) continuous_const) fun k => (h1 _).trans (hd k)
  ext a
  rw [← h1, h2, MonoidHom.one_apply]


omit [TopologicalSpace B] [T2Space B] in
theorem eq_one_of_unif {v : HeightOneSpectrum (𝓞 E)} (θ : (v.adicCompletion E)ˣ →* B)
    (h : ∀ x, IsUnifAt v x → θ x = 1) (x : (v.adicCompletion E)ˣ) : θ x = 1 := by
  obtain ⟨k, hk⟩ := exists_unif v
  generalize atFin v k = p at hk
  have hk' : Valued.v (p : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := hk
  have hx : Valued.v (x : v.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hu : IsUnifAt v (x * p ^ (WithZero.log (Valued.v (x : v.adicCompletion E)) + 1)) := by
    show Valued.v _ = _
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hk', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log hx]
    rw [← WithZero.exp_add]
    congr 1
    simp
  have := h _ hu
  rwa [map_mul, map_zpow, h p hk, one_zpow, mul_one] at this

theorem eq_one_of_frob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (B : Type) [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B] (φ : G E Ω →* B), Continuous φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ v, v ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G E Ω, IsFrob (F := E) A (normV v) σ → φ σ = 1) → φ = 1 := by
  intro E Ω _ _ _ _ _ art ha B _ _ _ _ φ hφ S hS
  have h : (liftAb φ hφ).comp art = 1 := by
    refine eq_one_of_away _ ((continuous_liftAb φ hφ).comp ha.quot.continuous) (fun k => ?_) S fun v hv => ?_
    · have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one]
    · refine eq_one_of_unif (((liftAb φ hφ).comp art).comp (localIdele E v)) fun x hx => ?_
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← e, liftAb_toAb, map_inv, hS v hv A hA σ hσ, inv_one]
  ext σ
  obtain ⟨x, hx⟩ := ha.quot.surjective (toAb E Ω σ)
  rw [← liftAb_toAb φ hφ, ← hx]
  exact DFunLike.congr_fun h x

end GlobalTheory.FrobDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.Determ

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (finiteSingle L v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_mulSingle (A := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
  have := (RestrictedProduct.continuous_inclusion hle).comp hf
  exact this

theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

theorem denseRange_atFin (v : HeightOneSpectrum (𝓞 L)) : DenseRange (atFin v) := by
  have hg : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    have : Set.range (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) = {0}ᶜ := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        exact u.ne_zero
      · intro hz
        exact ⟨Units.mk0 z hz, rfl⟩
    rw [this]
    exact isOpen_compl_singleton
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, x, hx, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap L v).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact x.ne_zero hk
  exact ⟨x, hx, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem exists_prod_inf_mul_finPart (a : Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, infIdele L w (y w)) * finPartI L a = a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    { toFun := fun x => x.1 w, map_one' := rfl, map_mul' := fun _ _ => rfl }
  refine ⟨fun w => Units.map (p w) a, ?_⟩
  have h : ((∏ w, infIdele L w (Units.map (p w) a) : Ideles L) : AdeleRing (𝓞 L) L) = ((a : AdeleRing (𝓞 L) L).1, 1) := by
    rw [Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w ((a : AdeleRing (𝓞 L) L).1 w)) = ι (fun w => (a : AdeleRing (𝓞 L) L).1 w)
    rw [← map_prod]
    exact congrArg ι (Finset.univ_prod_mulSingle (fun w : InfinitePlace L => ((a : AdeleRing (𝓞 L) L).1 w : w.Completion)))
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem loc_eq_one {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 L))
    (h : ∀ k, ψ (localIdele L v (atFin v k)) = 1) (x : (v.adicCompletion L)ˣ) : ψ (localIdele L v x) = 1 :=
  congrFun ((denseRange_atFin v).equalizer (g := fun x => ψ (localIdele L v x)) (h := fun _ => 1)
    (hψ.comp (continuous_localIdele v)) continuous_const (funext h)) x

theorem inf_eq_one {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ) (h : ∀ k, ψ (infDiag k) = 1)
    (y : ∀ w : InfinitePlace L, (w.Completion)ˣ) : ψ (∏ w, infIdele L w (y w)) = 1 := by
  refine congrFun ((GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer
    (g := fun y : ∀ w : InfinitePlace L, (w.Completion)ˣ => ψ (∏ w, infIdele L w (y w))) (h := fun _ => 1)
    (hψ.comp (continuous_finsetProd _ fun w _ =>
      (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))) continuous_const (funext fun k => ?_)) y
  have h1 := h k
  unfold infDiag at h1
  rw [MonoidHom.finsetProd_apply] at h1
  exact h1

theorem eq_one_of_components {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ)
    (hf : ∀ v k, ψ (localIdele L v (atFin v k)) = 1) (hi : ∀ k, ψ (infDiag k) = 1) (a : Ideles L) : ψ a = 1 := by
  obtain ⟨S, n, u, hu, rfl, -⟩ := exists_prod_unif_mul_unitIdl L a
  obtain ⟨y, hy⟩ := exists_prod_inf_mul_finPart u
  have h1 : ψ (finPartI L u) = 1 :=
    GlobalTheory.Mem.LocTriv.eq_one_of_local L ψ hψ _ (finPartI_mem_unitIdl.2 hu) (fun _ => rfl) fun v x _ => loc_eq_one hψ v (hf v) x
  rw [← hy, map_mul, map_mul, h1, inf_eq_one hψ hi, map_prod, mul_one, mul_one]
  exact Finset.prod_eq_one fun v _ => by
    rw [map_zpow]
    exact (congrArg (fun z : ℂˣ => z ^ n v) (hf v (unif v))).trans (one_zpow _)

end GlobalTheory.Mem.Chr.Determ
end
end

