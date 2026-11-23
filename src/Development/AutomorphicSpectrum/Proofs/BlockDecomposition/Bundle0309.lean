module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0293
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0294
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0278
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0295
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormulaStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_degree_formula : MulF → MulI → LogAbsBasic → FinSupp → DegAdelic := by
  first | exact @GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | exact GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | (intros; apply GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AppendCons
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Map
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}

theorem d_cup_one (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) {a m : ℕ} (h : 1 + a = m) (y : CH.Cn F₂ a) :
    CH.d F₃ m (P.cupC h b y) = -P.cupC (by omega : 1 + (a + 1) = m + 1) b (CH.d F₂ a y) := by
  rw [CrystallineSemistableComparison.P.leibniz, hb]
  simp

def cupMap (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) (a : ℕ) :
    CH.H F₂ a →ₗ[R] CH.H F₃ (a + 1) :=
  Submodule.mapQ _ _ ((((P.cupC (Nat.add_comm 1 a) b).comp (Submodule.subtype _))).codRestrict _ fun y => by
    change CH.d F₃ (a + 1) (P.cupC (Nat.add_comm 1 a) b y.1) = 0
    rw [d_cup_one P b hb]
    have : CH.d F₂ a y.1 = 0 := y.2
    rw [this, map_zero, neg_zero]) (by
      intro y hy
      change P.cupC (Nat.add_comm 1 a) b y.1 ∈ (CH.cx F₃).B (a + 1)
      have hy' : y.1 ∈ (CH.cx F₂).B a := hy
      cases a with
      | zero =>
        have : y.1 = 0 := hy'
        rw [this, map_zero]
        exact Submodule.zero_mem _
      | succ m =>
        obtain ⟨t, ht⟩ := hy'
        refine ⟨-P.cupC (Nat.add_comm 1 m) b t, ?_⟩
        change CH.d F₃ _ _ = _
        rw [map_neg, d_cup_one P b hb, neg_neg]
        change P.cupC _ b (CH.d F₂ m t) = _
        exact congrArg _ ht)

theorem cupMap_cls (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) {a : ℕ} (y : CH.Cn F₂ a)
    (hy : CH.d F₂ a y = 0) (hz : CH.d F₃ (a + 1) (P.cupC (Nat.add_comm 1 a) b y) = 0) :
    cupMap P b hb a ((CH.cx F₂).cls y hy) = (CH.cx F₃).cls (P.cupC (Nat.add_comm 1 a) b y) hz := rfl

def castH (F : C ⥤ ModuleCat.{0} R) {W W' : ObjectProperty C} (h : W = W') (j : ℕ) : HU F W' j ≃ₗ[R] HU F W j := by
  subst h
  exact LinearEquiv.refl R _

end Map

section Sch
variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem append_cons {M : Type*} {a : ℕ} (t : M) (g : Fin a → M) :
    Fin.append ![t] g ∘ Fin.cast (Nat.add_comm 1 a).symm = (Fin.cons t g : Fin (a + 1) → M) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · have e : Fin.cast (Nat.add_comm 1 a).symm (0 : Fin (a + 1)) = Fin.castAdd a (0 : Fin 1) := Fin.ext (by simp)
    simp only [Function.comp, e, Fin.append_left, Fin.cons_zero]
    rfl
  · have e : Fin.cast (Nat.add_comm 1 a).symm k.succ = Fin.natAdd 1 k := Fin.ext (by simp [Nat.add_comm])
    simp only [Function.comp, e, Fin.append_right, Fin.cons_succ]

theorem form_cup' (hFC : FormCup) {a c : ℕ} (hc : 1 + a = c) (g₁ g₀ : Sec q V) (t : Sec q V) (g : Fin a → Sec q V)
    (x : CH.Cn ((inU q V).ι ⋙ G q 1) 1) (y : CH.Cn ((inU q V).ι ⋙ G q a) a) (hx : CH.d _ 1 x = 0) (hy : CH.d _ a y = 0)
    (h₁ : IsForm q V (a := 1) g₁ ![t] ((CH.cx _).cls x hx)) (h₂ : IsForm q V g₀ g ((CH.cx _).cls y hy)) :
    ∃ hz, IsForm q V (a := c) (g₁ * g₀) (Fin.append ![t] g ∘ Fin.cast hc.symm)
      ((CH.cx ((inU q V).ι ⋙ G q c)).cls (cupU q (inU q V) hc hc x y) hz) := by
  subst hc
  exact hFC K Z q V 1 a g₁ g₀ ![t] g x y hx hy h₁ h₂

theorem cup_form (hFL : FormLaws) (hFU : FormUniq) (hFC : FormCup) {a : ℕ}
    (E₂ : Om K (Sec q V) a →ₗ[K] HV q V a a) (E₃ : Om K (Sec q V) (a + 1) →ₗ[K] HV q V (a + 1) (a + 1))
    (h₂ : IsOm q V a E₂) (h₃ : IsOm q V (a + 1) E₃) (g₁ t : Sec q V) (b : CH.Cn ((inU q V).ι ⋙ G q 1) 1)
    (hb : CH.d _ 1 b = 0) (hf : IsForm q V (a := 1) g₁ ![t] ((CH.cx _).cls b hb))
    (w : Om K (Sec q V) a →ₗ[Sec q V] Om K (Sec q V) (a + 1))
    (hw : ∀ g₀ (g : Fin a → Sec q V), w (form K g₀ g) = form K g₀ (Fin.cons t g))
    (y : CH.Cn ((inU q V).ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q V) a)
    (hcls : (CH.cx _).cls y hy = E₂ ω)
    (hz : CH.d ((inU q V).ι ⋙ G q (a + 1)) (a + 1) (cupU q (inU q V) (Nat.add_comm 1 a) (Nat.add_comm 1 a) b y) = 0) :
    (CH.cx ((inU q V).ι ⋙ G q (a + 1))).cls (cupU q (inU q V) (Nat.add_comm 1 a) (Nat.add_comm 1 a) b y) hz =
      E₃ (g₁ • w ω) := by
  let P := pairU (grOk (smFun Z q) (Nat.add_comm 1 a)).pair (inU q V)
  have key : (cupMap P b hb a).restrictScalars K ∘ₗ E₂ = E₃ ∘ₗ ((g₁ • w).restrictScalars K) := by
    refine lin_ext hFL _ _ fun g₀ v => ?_
    obtain ⟨⟨y', hy'⟩, hyy⟩ := Submodule.Quotient.mk_surjective _ (E₂ (form K g₀ v))
    have hy'' : CH.d _ a y' = 0 := hy'
    have hc' : (CH.cx _).cls y' hy'' = E₂ (form K g₀ v) := hyy
    have hI := h₂ g₀ v
    rw [← hc'] at hI
    obtain ⟨hz', hform⟩ := form_cup' hFC (Nat.add_comm 1 a) g₁ g₀ t v b y' hb hy'' hf hI
    rw [append_cons] at hform
    have hu := ((hFU K Z q V).2 (a + 1) (g₁ * g₀) (Fin.cons t v)).unique hform (h₃ _ _)
    change cupMap P b hb a (E₂ (form K g₀ v)) = E₃ (g₁ • w (form K g₀ v))
    rw [← hc', hw]
    refine (cupMap_cls P b hb y' hy'' hz').trans (hu.trans ?_)
    congr 1
    exact mul_smul _ _ _
  have := LinearMap.congr_fun key ω
  change cupMap P b hb a (E₂ ω) = E₃ (g₁ • w ω) at this
  rw [← hcls] at this
  exact (cupMap_cls P b hb y hy hz).symm.trans this

end Sch

end GlobalTheory.CompanionTheory.RelKill
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSubsetSupportProper
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.ClosedSub

theorem closed_subset_support_proper {A : Type} [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (O : X.Opens) (C : Set X) (hC : IsClosed C)
    (hCO : C ⊆ (O : Set X)) :
    ∃ T' : (O : Scheme.{0}).IdealSheafData,
      (T'.support : Set (O : Scheme.{0})) = O.ι.base ⁻¹' C ∧
        IsProper (T'.subschemeι ≫ O.ι ≫ (X ↘ Spec (.of A))) := by
  have hC' : IsClosed (O.ι.base ⁻¹' C) := hC.preimage O.ι.continuous
  refine ⟨Scheme.IdealSheafData.vanishingIdeal ⟨_, hC'⟩, by simp, ?_⟩
  set T' := Scheme.IdealSheafData.vanishingIdeal (X := (O : Scheme.{0})) ⟨_, hC'⟩
  have hrange : Set.range (T'.subschemeι ≫ O.ι) = C := by
    have h : Set.range (T'.subschemeι ≫ O.ι) = O.ι '' Set.range T'.subschemeι := by
      rw [← Set.range_comp]
      rfl
    rw [h, Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change O.ι '' (O.ι ⁻¹' C) = C
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact Set.inter_eq_left.mpr hCO
  have : IsClosedImmersion (T'.subschemeι ≫ O.ι) :=
    IsClosedImmersion.of_isPreimmersion _ (hrange ▸ hC)
  rw [← Category.assoc]
  infer_instance

end GlobalTheory.CompanionTheory.GE.ClosedSub
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionSubobjectStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_restriction_subobject : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ S : ℕ → Subobject E, ClosedSys I E S → ∀ Sb : ℕ → Subobject P, (∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W), x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → (∀ e, Bb ⊔ powSub I P (e + 1) = Sb e) → ∃ B : Subobject E, (B : (O : Scheme.{0}).Modules).IsQuasicoherent ∧ (∀ e, B ⊔ powSub I E (e + 1) = S e) ∧ ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W) := by
  first | exact @GlobalTheory.CompanionTheory.GE.ImageOpen.image_on_open | exact GlobalTheory.CompanionTheory.GE.ImageOpen.image_on_open | (intros; apply GlobalTheory.CompanionTheory.GE.ImageOpen.image_on_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientReductionFirstChernClassTateTwist
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ReductionFirstChern

open GlobalTheory.CompanionTheory.CocCls

section Ring

variable {S S' : Type} [CommRing S] [CommRing S'] {J : Ideal S} {J' : Ideal S'}

theorem dpow_mem_pdP (δ : DividedPowers J) {x : S} (hx : x ∈ J) {k r : ℕ} (h : r ≤ k) : δ.dpow k x ∈ pdP δ r :=
  Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simpa using h, by simp⟩

theorem dlog_trunc (δ : DividedPowers J) {s N : ℕ} (hs : pdP δ s = ⊥) (h : s ≤ N) {v : S} (hv : v - 1 ∈ J) :
    B.dlog δ N v = B.dlog δ s v := by
  unfold B.dlog
  refine (Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_).symm
  have h1 : δ.dpow (k + 1) (v - 1) ∈ pdP δ s := dpow_mem_pdP δ hv (by
    have : s ≤ k := by simpa using hk
    omega)
  rw [hs, Ideal.mem_bot] at h1
  rw [h1, mul_zero]

theorem dlog_red {δ : DividedPowers J} {δ' : DividedPowers J'} {f : S →+* S'} (hf : IsDPMorphism δ δ' f) {s N : ℕ}
    (hs : pdP δ s = ⊥) (hN : ∀ k, N ≤ k → (k.factorial : S') = 0) {v : S} (hv : v - 1 ∈ J) :
    f (B.dlog δ s v) = B.dlog δ' N (f v) := by
  rw [← dlog_trunc δ hs (le_max_left s N) hv, dlog_map hf _ hv]
  exact GlobalTheory.CompanionTheory.FirstChernClassFactorial.dlog_eq_of_factorial δ' (le_max_right s N) hN _

theorem factorial_quot {l : ℕ} (hl : l ≠ 0) (n k : ℕ) (hk : l * n ≤ k) :
    (k.factorial : S ⧸ Ideal.span {(l : S) ^ n}) = 0 := by
  obtain ⟨a, ha⟩ := (GlobalTheory.CompanionTheory.FirstChernClassFactorial.pow_dvd_factorial_mul l (Nat.pos_of_ne_zero hl) n).trans (Nat.factorial_dvd_factorial hk)
  rw [ha, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : S) ^ n})), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Ring

section Lift

variable {O A R : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {s : ℕ} {𝒱 : Set X.Opens}
  {C : Type 1} [Category.{0} C] (g : C ⥤ (TS γ q l s 𝒱).FullSubcategory) {D : E.LineData X}

def redLift (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D) :
    B.CLift (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) (g ⋙ redG q s d 𝒱) D where
  p T := Spec.map (CommRingCat.ofHom (qBar (g.obj T).obj l n)) ≫ Lf.p T
  hp T := by
    rw [Category.assoc, Lf.hp]
    rfl
  w {T T'} φ := Units.map (Ideal.Quotient.mk (lnT (g.obj T').obj l n)).toMonoidHom (Lf.w φ)
  hw {T T'} φ h := by
    have e : B.thSp (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) ((g ⋙ redG q s d 𝒱).map φ) ≫ Spec.map (CommRingCat.ofHom (qBar (g.obj T).obj l n)) ≫ Lf.p T =
        Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ (B.thSp (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) ((g ⋙ (TS γ q l s 𝒱).ι).map φ) ≫ Lf.p T) := by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      unfold B.thSp
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
    have h0 := hh Lf φ
    have h2 : (Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ (B.thSp (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) ((g ⋙ (TS γ q l s 𝒱).ι).map φ) ≫ Lf.p T)) ≫ D.f =
        (Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ Lf.p T') ≫ D.f := by
      rw [Category.assoc, h0, Category.assoc]
    have h3 := uq_map D (qBar (g.obj T').obj l n) _ _ h0 h2
    have h4 := uq_congr D e rfl h h2
    have h5 := Lf.hw φ h0
    change _ = (uq D _ _ h).val
    rw [h4, h3]
    change _ = qBar (g.obj T').obj l n (uq D _ _ h0).val
    refine Eq.trans ?_ (congrArg (qBar (g.obj T').obj l n) h5)
    rfl

theorem r_red (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) :
    (B.CLift.r (redLift d g Lf) σ).val = Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n) (B.CLift.r Lf σ).val := by
  have h2 : B.CLift.r (redLift d g Lf) σ =
      Units.map (Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n)).toMonoidHom (B.CLift.r Lf σ) := by
    unfold B.CLift.r
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [h2]
  rfl

theorem r_sub (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) : (B.CLift.r Lf σ).val - 1 ∈ (g.obj (σ.obj (Fin.last 2))).obj.J := by
  have hfg : σ.map' 0 2 = σ.map' 0 1 ≫ σ.map' 1 2 := σ.map'_comp 0 1 2
  have h0 : B.CLift.r Lf σ = Rf Lf (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 1 ≫ σ.map' 1 2) := by
    rw [← hfg]
    rfl
  have h1 : red (σ.obj (Fin.last 2)) (g ⋙ (TS γ q l s 𝒱).ι) (B.CLift.r Lf σ) = 1 := by
    rw [h0]
    exact red_Rf Lf _ _
  exact sub_one_mem h1

theorem coc_red {Λ : Type} [CommRing Λ] (c : Λ →+* R)
    (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) :
    B.CLift.coc (redLift d g Lf) c (l * n) σ =
      Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n) (B.CLift.coc Lf (RingHom.id A) s σ) := by
  have e1 := dlog_red (redδ_dp (g.obj (σ.obj (Fin.last 2))).obj (g.obj (σ.obj (Fin.last 2))).property.1 n) (s := s) (N := l * n)
    (g.obj (σ.obj (Fin.last 2))).property.1.1 (fun k hk => factorial_quot d.hl n k hk) (r_sub g Lf σ)
  exact (congrArg _ (r_red d g Lf σ)).trans e1.symm

end Lift

section Top

variable {b : Base} {L : b.Fun}

theorem idF_ext {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a a' : IdF A}
    (h : a.S = a'.S) : a = a' := by
  cases a
  cases a'
  cases h
  rfl

theorem stdI_top (Q : ObjectProperty (Thick L)) : stdI Q (some 0) 0 = IdF.top _ :=
  idF_ext (funext fun T => top_unique (le_trans (le_of_eq T.obj.pdPow_zero.symm) le_sup_left))

theorem bij_top {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {a e : IdF (sP Q).A} {a' e' : IdF (sP Q').A}
    (ha : a = IdF.top _) (ha' : a' = IdF.top _) (h1 : (incl h).Le a a') (h2 : (incl h).Le e e') (j : ℕ)
    (H : Function.Bijective (((incl h).sq h1 h2).pull j)) :
    Function.Bijective (((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) h2).pull j) := by
  subst ha ha'
  exact H

end Top

theorem coefficientReduction_firstChernClass_tateTwist : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))
    (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∀ (x : CH.H (B.OM (nlFun δ l X q κ) c) 2) (z : HO (TS γ q l s {⊤}) 2),
    B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) D c (l * n) x → IsFirstChernThickening (TS γ q l s {⊤}) D s z →
    redM (TS γ q l s {⊤}) none ((l : A) ^ n) 2 z = (redMor q s d {⊤} c lam hc none).pull 2 x := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s c lam hc D hD x z hx hz
  let Q := TS γ q l s {⊤}
  let Q' := TS γ q l s (𝒱D D)
  have h : Q' ≤ Q := fun T hT => ⟨hT.1, ⊤, rfl, GlobalTheory.CompanionTheory.CrystallineChernClass.inU_top T⟩
  let g : Q'.FullSubcategory ⥤ Q.FullSubcategory := ObjectProperty.ιOfLE h
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun γ 0 X q (κA O I)))) := Or.inl ⟨rfl, l, s, rfl⟩
  have hinj := bij_top h (stdI_top Q) (stdI_top Q') _ (incl_std h none ((l : A) ^ n)) 2
    ((_root_.GlobalTheory.CompanionTheory.NlZar.zariski_descent (TF l s) hU (𝒱D D) {⊤} h (by rintro W rfl; rw [hD]) 2).2.1 (some 0) none 0 ((l : A) ^ n))
  obtain ⟨Lf⟩ := _root_.GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ Q.ι) D (fun T =>
    GlobalTheory.CompanionTheory.CrystallineChernClass.st_le_lifts (γ := γ) (p := 0) (q := q) (κ := κA O I) D T.obj ⟨trivial, T.property.2⟩)
  obtain ⟨hz1, hcl1⟩ := hz Q'.FullSubcategory g (fun T => T.property.2) Lf
  let Lr := redLift d g Lf
  obtain ⟨hz2, hcl2⟩ := hx Q'.FullSubcategory (g ⋙ redG q s d {⊤}) Lr
  apply hinj.1
  let P := (incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h none ((l : A) ^ n))
  let M₁ := (toSq (IdF.top _) (stdI Q none ((l : A) ^ n)) fun _ => rfl).comp P
  let M₂ := (redMor q s d {⊤} c lam hc none).comp (σ'' := lam) P
  let m₁ : CH.Mor (g ⋙ CH.modF (sP Q).A) (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) (RingHom.id A) :=
    { G := 𝟭 _, τ := fun T => M₁.τ T, nat := fun φ x => M₁.nat φ x }
  let m₂ : CH.Mor ((g ⋙ redG q s d {⊤}) ⋙ B.OM (nlFun δ l X q κ) c) (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) lam :=
    { G := 𝟭 _, τ := fun T => M₂.τ T, nat := fun φ x => M₂.nat φ x }
  have hL : P.pull 2 (redM Q none ((l : A) ^ n) 2 z) = m₁.pull 2 ((CH.Mor.restrict (CH.modF (sP Q).A) g).pull 2 z) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  have hR : P.pull 2 ((redMor q s d {⊤} c lam hc none).pull 2 x) =
      m₂.pull 2 ((CH.Mor.restrict (B.OM (nlFun δ l X q κ) c) (g ⋙ redG q s d {⊤})).pull 2 x) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have hE : m₁.pullC 2 (Lf.coc (RingHom.id A) s) = m₂.pullC 2 (Lr.coc c (l * n)) := by
    funext σ
    have e := coc_red d g c Lf σ
    have t : ∀ (T : Q'.FullSubcategory) (b : (g.obj T).obj.B), m₁.τ T b = m₂.τ T (Ideal.Quotient.mk (lnT (g.obj T).obj l n) b) :=
      fun _ _ => rfl
    exact (t _ _).trans (congrArg (m₂.τ _) e.symm)
  have hb1 : CH.d _ 2 (m₁.pullC 2 (Lf.coc (RingHom.id A) s)) = 0 :=
    (m₁.d_pullC 2 _).trans ((congrArg _ hz1).trans (map_zero _))
  have hb2 : CH.d _ 2 (m₂.pullC 2 (Lr.coc c (l * n))) = 0 :=
    (m₂.d_pullC 2 _).trans ((congrArg _ hz2).trans (map_zero _))
  have a1 := CrystallineSemistableComparison.P.mapH_cls m₁.hom 2 _ hz1 hb1
  have a2 := CrystallineSemistableComparison.P.mapH_cls m₂.hom 2 _ hz2 hb2
  have key : ∀ (w w' : CH.Cn (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) 2) (k : CH.d _ 2 w = 0) (k' : CH.d _ 2 w' = 0),
      w = w' → (CH.cx _).cls w k = (CH.cx _).cls w' k' := by
    rintro _ _ _ _ rfl
    rfl
  exact hL.trans ((congrArg (m₁.pull 2) hcl1.symm).trans (a1.trans ((key _ _ hb1 hb2 hE).trans
    (a2.symm.trans ((congrArg (m₂.pull 2) hcl2).trans hR.symm)))))

end GlobalTheory.CompanionTheory.ReductionFirstChern
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentNoetherianMaximalSubsheaf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE

theorem eq_of_le_of_secs_subset {X : Scheme.{0}} {P : X.Modules} {ι : Type*} (𝒰 : ι → X.Opens)
    (hcov : TopologicalSpace.IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i)) {M B : Subobject P}
    (hM : (M : X.Modules).IsQuasicoherent) (hB : (B : X.Modules).IsQuasicoherent) (hle : M ≤ B)
    (h : ∀ i, secs B (𝒰 i) ⊆ secs M (𝒰 i)) : B = M := by
  haveI := hM
  haveI := hB
  have hepi : Epi (Subobject.ofLE M B hle) := by
    refine (GlobalTheory.QCoh.epi_iff_affineCover 𝒰 hcov haff _).2 fun i y ↦ ?_
    obtain ⟨x, hx⟩ := h i ⟨y, rfl⟩
    refine ⟨x, GlobalTheory.QCoh.injective_app_of_mono B.arrow _ ?_⟩
    change (Subobject.ofLE M B hle ≫ B.arrow).app _ x = _
    rw [Subobject.ofLE_arrow]
    exact hx
  haveI hmono : Mono (Subobject.ofLE M B hle) := mono_of_mono_fac (Subobject.ofLE_arrow hle)
  haveI : IsIso (Subobject.ofLE M B hle) := isIso_of_mono_of_epi _
  refine le_antisymm (Subobject.le_of_comm (inv (Subobject.ofLE M B hle)) ?_) hle
  rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow]

theorem exists_maximal_qcoh_subobject {X : Scheme.{0}} [IsNoetherian X] {P : X.Modules}
    (hP : IsCoherent P) (F : Set (Subobject P)) (hF : F.Nonempty)
    (hq : ∀ B ∈ F, (B : X.Modules).IsQuasicoherent) :
    ∃ M ∈ F, ∀ B ∈ F, M ≤ B → B = M := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ U.1.isOpen) (fun x _ ↦ by
      obtain ⟨U, ⟨V, hV, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxU⟩)
  let 𝒰 : t → X.Opens := fun i ↦ (i.1 : X.Opens)
  have hcov : TopologicalSpace.IsOpenCover 𝒰 := top_le_iff.1 fun x _ ↦ by
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩
  have haff : ∀ i, IsAffineOpen (𝒰 i) := fun i ↦ i.1.2
  haveI hnoeth : ∀ i : t, IsNoetherianRing Γ(X, 𝒰 i) := fun i ↦
    IsLocallyNoetherian.component_noetherian ⟨𝒰 i, haff i⟩
  haveI hfin : ∀ i : t, Module.Finite Γ(X, 𝒰 i) Γ(P, 𝒰 i) := fun i ↦ hP.2 _ (haff i)
  haveI hwf : ∀ i : t, WellFoundedLT (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ := fun i ↦
    inferInstanceAs (WellFoundedGT (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i)))
  let g : Subobject P → ∀ i : t, (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ :=
    fun B i ↦ OrderDual.toDual (secsSub B (𝒰 i))
  have hmin := (wellFounded_lt (α := ∀ i : t, (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ)).has_min
    (g '' F) (hF.image g)
  obtain ⟨_, ⟨M, hM, rfl⟩, hmin⟩ := hmin
  refine ⟨M, hM, fun B hB hle ↦ ?_⟩
  have hle' : g B ≤ g M := fun i ↦ by
    change secsSub M (𝒰 i) ≤ secsSub B (𝒰 i)
    rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.ofLE M B hle).app (𝒰 i) x, ?_⟩
    rw [← Subobject.ofLE_arrow hle]
    rfl
  have heq : g B = g M := by
    by_contra hne
    exact hmin _ ⟨B, hB, rfl⟩ (lt_of_le_of_ne hle' hne)
  refine eq_of_le_of_secs_subset 𝒰 hcov haff (hq M hM) (hq B hB) hle fun i ↦ ?_
  have hi : secsSub B (𝒰 i) = secsSub M (𝒰 i) := congrFun heq i
  intro y hy
  have hy' : y ∈ secsSub B (𝒰 i) := hy
  rw [hi] at hy'
  exact hy'

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBoundStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_submodule_bound : WedgeF → WedgeI → WedgeSub → FinSupp → DegBasisG → TwoBases → DegSubmod := by
  first | exact @GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | exact GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | (intros; apply GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumSystemDescendsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.direct_sum_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (A : I → Sy.{1} K ι), (∀ i, (A i).Desc) → (sumSy A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | exact GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc <;> assumption)
end

