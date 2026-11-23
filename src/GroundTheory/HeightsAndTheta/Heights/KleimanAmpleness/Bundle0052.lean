module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AltSumEqOfEventually
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

noncomputable section

section Poly

variable {K : Type}

theorem eval_bind₁_shift (p : MvPolynomial K ℚ) (a z : K → ℚ) :
    eval z (bind₁ (fun k => X k - C (a k)) p) = eval (z - a) p := by
  show eval₂Hom (RingHom.id ℚ) z _ = _
  rw [eval₂Hom_bind₁]
  have hfun : (fun i => eval₂Hom (RingHom.id ℚ) z (X i - C (a i))) = z - a := funext fun k => by simp
  rw [hfun]
  rfl

theorem altSum_eq_of_eventually (p : MvPolynomial K ℚ) {n : ℕ} (δ : Fin n → K → ℤ) (D : ℚ)
    (h : ∀ᶠ m : K → ℤ in atTop,
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D)
    (z : K → ℤ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((z - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
  classical
  let q : MvPolynomial K ℚ := ∑ T : Finset (Fin n),
    C ((-1 : ℚ) ^ T.card) * bind₁ (fun k => X k - C (((∑ i ∈ T, δ i) k : ℤ) : ℚ)) p
  have hq : ∀ w : K → ℤ, eval (fun k => (w k : ℚ)) q =
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((w - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [q, map_sum, map_mul, eval_C, eval_bind₁_shift]
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 3
    funext k
    simp only [Pi.sub_apply, Int.cast_sub]
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp h
  let s : K → Set ℚ := fun k => (fun t : ℤ => (t : ℚ)) '' Set.Ici (m₀ k)
  have hs : ∀ k, (s k).Infinite := fun k =>
    (Set.Ici_infinite (m₀ k)).image (fun a _ b _ hab => Int.cast_injective hab)
  have hqD : q = C D := by
    refine funext_set s hs fun w hw => ?_
    have hw' : ∀ k, ∃ t : ℤ, m₀ k ≤ t ∧ (t : ℚ) = w k := fun k => hw k (Set.mem_univ k)
    choose m hm1 hm2 using hw'
    have hwm : w = fun k => (m k : ℚ) := funext fun k => (hm2 k).symm
    rw [hwm, hq, eval_C]
    exact hm₀ m hm1
  rw [← hq, hqD, eval_C]

end Poly

theorem NumModel.proof (hT : TensorRealise.Statement) (hS : SectionsPoly.Statement) (hD : ModelDim.Statement) :
    NumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n L δ hL hsub
  classical
  obtain ⟨i₀, hi₀⟩ := hmod.1 k₀
  have hj : x (e i₀) ≠ 0 := by
    rw [hx]
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi₀
  have hP := isMultiProjPrime_mIdealOver (S := F) y hmod.1
  have hdim := (hD F K ι Ω y k₀ N e x hx hmod n).mp hsub
  obtain ⟨p, hpH, hpS⟩ := hS F K ι Ω y k₀ hmod
  have hMD := (FieldNumbers.MixedDiffConst.full F K ι (mIdealOver F y) hP.multiHomog hP.relevant n hdim).1 δ
  set D := NumbersDVR.intNum F (mIdealOver F y) δ with hD_def

  have hev : ∀ᶠ m : K → ℤ in atTop, ∑ T : Finset (Fin n),
      (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
    have h2 : ∀ T : Finset (Fin n), ∀ᶠ m : K → ℤ in atTop,
        (NumbersDVR.hilbFn (mIdealOver F y) (m - ∑ i ∈ T, δ i) : ℚ) =
          eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := fun T =>
      ((tendsto_atTop_add_const_right atTop (-(∑ i ∈ T, δ i)) tendsto_id).eventually hpH).mono
        fun m hm => by simpa only [id, sub_eq_add_neg] using hm
    filter_upwards [hMD, eventually_all.mpr h2] with m h1 h2
    rw [mixedDiff_eq_sum] at h1
    have h1' := congrArg (Int.cast : ℤ → ℚ) h1
    push_cast at h1'
    rw [← h1']
    exact Finset.sum_congr rfl fun T _ => by rw [h2 T]
  have hall := altSum_eq_of_eventually p δ (D : ℚ) hev

  have hsecs : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      ((restrLen (primeOf (S := F) x)
          ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys F x (c : ℤ))) : ℤ) : ℚ) =
        eval (fun k => (((∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k : ℤ) : ℚ)) p := fun T => by
    filter_upwards [hT F K ι Ω y k₀ N e x hx hmod n L δ hL T, hpS (∑ i ∈ T, δ i)] with c h1 h2
    rw [restrLen_primeOf_eq_finrank x hj, h1, ← h2]
    simp
  have hfin : ∀ᶠ c : ℕ in atTop, interSum (primeOf (S := F) x) (fun i => (L i).toSubSystem) c = D := by
    filter_upwards [eventually_all.mpr hsecs] with c hc
    apply Int.cast_injective (α := ℚ)
    rw [interSum, ← hall (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)]
    push_cast
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hcard : Tᶜ.card = n - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    have hvec : (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) - ∑ i ∈ Tᶜ, δ i =
        ∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
      rw [← Finset.sum_add_sum_compl T δ]
      abel
    rw [hc T, hcard, hvec]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hfin.mono fun c h => h.symm)).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHcSubsingletonOfBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart Cell CechC cellMon cechZc cechBc)

noncomputable section

def eulerChar (F : Type) [Field F] {K : Type} [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) : ℚ :=
  ∑ i ∈ Finset.range (∑ k, (Fintype.card (ι k) - 1) + 1),
    (-1 : ℚ) ^ i * (Module.finrank F (cechHc ι (quotPart F V) m i) : ℚ)

def EulerVar.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (v : Σ k, ι k),
    NumbersDVR.IsMultiHomogIdeal V →
    (∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F V) m i)) →
    (∀ (m : K → ℤ) (i : ℕ),
      FiniteDimensional F (cechHc ι (quotPart F (V.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}))) m i)) →
    (∀ (m : K → ℤ) (i : ℕ),
      FiniteDimensional F (cechHc ι (quotPart F (V ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) m i)) →
    ∀ m : K → ℤ, eulerChar F ι V m =
      eulerChar F ι (V.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) (m - Pi.single v.1 1) +
        eulerChar F ι (V ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) m

section Vanish

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]


omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in
theorem subsingleton_loc_of_block {V : Ideal (MvPolynomial (Σ k, ι k) F)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ V) (I : ∀ k, Finset (ι k)) (hI : (I k).Nonempty) :
    Subsingleton (LocalizedModule (cellMon F I) (MvPolynomial (Σ k, ι k) F ⧸ V)) := by
  obtain ⟨i, hi⟩ := hI
  have ht : (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ cellMon F I :=
    Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hz : ∀ x : LocalizedModule (cellMon F I) (MvPolynomial (Σ k, ι k) F ⧸ V), x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h a s =>
      rw [← LocalizedModule.zero_mk (1 : cellMon F I), LocalizedModule.mk_eq]
      refine ⟨⟨_, ht⟩, ?_⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp only [one_smul, smul_zero]
      rw [Submonoid.smul_def]
      change (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) • Ideal.Quotient.mk V a = 0
      rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact V.mul_mem_right _ (hk i)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem cechHc_subsingleton_of_block {V : Ideal (MvPolynomial (Σ k, ι k) F)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ V) (m : K → ℤ) (n : ℕ) :
    Subsingleton (cechHc ι (quotPart F V) m n) := by
  have hI : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, Subsingleton (LocalizedModule (cellMon F I.1) (MvPolynomial (Σ k, ι k) F ⧸ V)) :=
    fun I => subsingleton_loc_of_block hk I.1 (I.2.1 k)
  have : Subsingleton (CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) :=
    ⟨fun f g => funext fun I => (hI I).elim _ _⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

end Vanish

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellPosExact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]

def CellPosExact (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) : Prop :=
  ∀ q : ℕ, ∀ s ∈ cellCOf S G (q + 1), cellD S y (q + 1) s = 0 →
    ∃ t ∈ cellCOf S G q, cellD S y q t = s

end

def CellContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (G : (∀ k, Finset (ι k)) → Submodule S Ω) (c : ∀ k, ι k),
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I → G I = ⊥) →
    (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' → G I ≤ G I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
      G (Function.update I k (insert (c k) (I k))) = G I) →
    CellPosExact S y G

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver secOver secMOver)

noncomputable section

section OneBlock

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

variable {κ : Type} [Fintype κ]


omit [Fintype κ] in
theorem chartRingOver_oneBlock_eq (x : κ → Ω) (c : Unit → κ) :
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Algebra.adjoin F (Set.range fun i => x i / x (c ())) := by
  unfold chartRingOver
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩


omit [Fintype κ] in
theorem mem_secOver_oneBlock (x : κ → Ω) (n : ℤ) (t : Ω) :
    t ∈ secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) ↔
      ∀ j, x j ≠ 0 → t * x j ^ (-n) ∈ Algebra.adjoin F (Set.range fun i => x i / x j) := by
  unfold secOver
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Finset.univ_unique,
    Finset.prod_singleton, Subalgebra.mem_toSubmodule, chartRingOver_oneBlock_eq]
  constructor
  · intro h j hj
    exact h (fun _ => j) (fun _ => hj)
  · intro h c hc
    exact h (c ()) (hc ())


omit [Fintype κ] in
theorem secOver_oneBlock_comp {κ' : Type} (σ : κ' ≃ κ) (x : κ → Ω) (n : ℤ) :
    secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (x ∘ σ)) (fun _ => n) = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secOver_oneBlock, mem_secOver_oneBlock]
  have hr : ∀ j', Set.range (fun i' => x (σ i') / x (σ j')) = Set.range (fun i => x i / x (σ j')) :=
    fun j' => σ.surjective.range_comp (fun i => x i / x (σ j'))
  simp only [Function.comp_apply]
  constructor
  · intro h j hj
    obtain ⟨j', rfl⟩ := σ.surjective j
    have := h j' hj
    rwa [hr] at this
  · intro h j' hj'
    rw [hr]
    exact h (σ j') hj'


omit [Fintype κ] in
theorem relDim_oneBlock_eq_iff (P : Ideal (MvPolynomial (Σ _ : Unit, κ) F)) (e : ℕ) :
    FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
      ringKrullDim (MvPolynomial (Σ _ : Unit, κ) F ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit]

end OneBlock

section FirstTyping

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}

theorem twistSys_secs_eq_secOver (x : Fin (N + 1) → Ω) (n : ℤ) :
    (Kleiman.twistSys F x n).secs = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secs_iff, mem_secOver_oneBlock]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  change t ∈ Kleiman.twistMod F x n (Kleiman.singleChart hj) ↔ _
  rw [Kleiman.twistMod_eq_span n _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]
  have hA : Kleiman.chartRing F x (Kleiman.singleChart hj) =
      Algebra.adjoin F (Set.range fun i => x i / x j) :=
    (chartRingOver_oneBlock x (fun _ => j) hj).symm.trans (chartRingOver_oneBlock_eq x (fun _ => j))
  rw [← hA]
  have hxn : x j ^ n ≠ 0 := zpow_ne_zero n hj
  constructor
  · rintro ⟨a, rfl⟩
    rw [Kleiman.chartRing_smul_def, zpow_neg, mul_assoc, mul_inv_cancel₀ hxn, mul_one]
    exact a.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [Kleiman.chartRing_smul_def]
    show t * x j ^ (-n) * x j ^ n = t
    rw [zpow_neg]
    exact inv_mul_cancel_right₀ hxn t

theorem mIdealOver_oneBlock (x : Fin (N + 1) → Ω) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) = Kleiman.primeOfOne (S := F) x := by
  have hc : ((MvPolynomial.uniqueAlgEquiv Ω Unit).toAlgHom.restrictScalars F).comp
      (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = (Kleiman.cone (S := F) x).comp (Kleiman.oneBlock (S := F) (N := N)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, Kleiman.cone, Kleiman.oneBlock, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  ext f
  rw [mIdealOver, RingHom.mem_ker, Kleiman.primeOfOne, Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  have h := congrArg (fun φ => φ f) hc
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [← h]
  exact (map_eq_zero_iff _ (MvPolynomial.uniqueAlgEquiv Ω Unit).injective).symm

theorem isSubvar_primeOf_iff (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) x) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have hX : ∀ i, (X i : Kleiman.Poly F N) ∈ Kleiman.primeOf (S := F) x ↔ x i = 0 := fun i => by
    rw [Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X F i), aeval_X]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.relevant
    exact ⟨⟨i, fun hx => hi ((hX i).mpr hx)⟩, h.dim⟩
  · rintro ⟨⟨i, hi⟩, hdim⟩
    exact ⟨inferInstance, fun p hp d => Kleiman.homogeneousComponent_mem_primeOf x hp d, le_rfl,
      ⟨i, fun h => hi ((hX i).mp h)⟩, hdim⟩

theorem isSubvar_iff_relDim (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ FieldNumbers.relDim (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  rw [isSubvar_primeOf_iff, relDim_oneBlock_eq_iff, mIdealOver_oneBlock, HilbertPositive.ringKrullDim_primeOfOne]

end FirstTyping

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FinrankSectionsOverEqH0
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver cechHc cechZc cechBc quotPart GlobalSectionsComparisonStatement)

noncomputable section

theorem altSum_eq_of_vanish (f : ℕ → ℕ) (B : ℕ) (h : ∀ i, 1 ≤ i → f i = 0) :
    ∑ i ∈ Finset.range (B + 1), (-1 : ℚ) ^ i * (f i : ℚ) = f 0 := by
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun i _ => by rw [h (i + 1) (by omega)]; simp]
  simp

theorem finrank_sectionsOver_eq_H0 (hB : GlobalSectionsComparisonStatement) {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K]
    {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (n : K → ℤ) :
    Module.finrank F (secOver F y n) = Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) n 0) := by
  obtain ⟨φ, hinj, hrange, -⟩ := hB F K ι Ω y n hy
  let e1 : ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) ≃ₗ[F] secOver F y n :=
    (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hbot : (cechBc ι (quotPart F (mIdealOver F y)) n 0).comap
      (cechZc ι (quotPart F (mIdealOver F y)) n 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  let e2 : cechHc ι (quotPart F (mIdealOver F y)) n 0 ≃ₗ[F] ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) :=
    Submodule.quotEquivOfEqBot _ hbot
  rw [← e1.finrank_eq, e2.finrank_eq]

theorem SectionsPoly.proof (hB : GlobalSectionsComparisonStatement) (hE : EulerPoly.Statement) (hM : MultiSerre.Statement)
    (hR : RayVanish.Statement) : SectionsPoly.Statement := by
  intro F _ K _ dK ι _ Ω _ _ y k₀ hmod
  let lo : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain rfl : dK = @LinearOrder.toDecidableEq K lo := Subsingleton.elim _ _
  have hV : NumbersDVR.IsMultiHomogIdeal (mIdealOver F y) := isMultiHomogIdeal_mIdealOver y
  obtain ⟨B, χ, -, -, hχ⟩ := hE F K ι (mIdealOver F y) hV
  have key : ∀ m : K → ℤ, (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) m i)) →
      (Module.finrank F (secOver F y m) : ℚ) = eval (fun k => (m k : ℚ)) χ := by
    intro m hm
    rw [← hχ m, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    refine (altSum_eq_of_vanish (fun i => Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) m i)) B
      fun i hi => ?_).symm
    have := hm i hi
    exact Module.finrank_zero_of_subsingleton
  refine ⟨χ, ?_, fun β => ?_⟩
  · filter_upwards [hM F K ι (mIdealOver F y) hV] with m hm
    rw [← hm.2, ← key m hm.1, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    push_cast
    rfl
  · filter_upwards [hR F K ι Ω y k₀ hmod β] with c hc
    exact key _ hc

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelRowExact.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      CellAugExact F y (fun I => cellSec F y γ (baseCell k₀ e J.1 I))
        (Submodule.span F (chartSecOver F y k₀ e γ J))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelGenerated.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ β : K → ℤ,
      ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

