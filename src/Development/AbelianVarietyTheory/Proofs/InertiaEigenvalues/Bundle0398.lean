module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnPrimePowerRootSystems
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isClosed_setOf_gal_apply_eq_padic (l : ℕ) [Fact l.Prime] (a b : Om l) :
    IsClosed {g : GQ l | g a = b} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (MulAction.stabilizer (GQ l) a : Set (GQ l)), ?_,
    (stabilizer_isOpen_of_isIntegral a).preimage (continuous_const.mul continuous_id), ?_⟩
  · intro h hh
    have hs : (g⁻¹ * h) a = a := hh
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hg ⊢
    intro hb
    apply hg
    rw [AlgEquiv.mul_apply] at hs
    have hga := congrArg g hs
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hga
    rw [← hga, hb]
  · show (g⁻¹ * g) a = a
    rw [inv_mul_cancel, AlgEquiv.one_apply]

theorem galois_transitive_on_root_systems_of_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ y z : ℕ → Om l, y 0 = ((π : ↥K.1) : Om l) → z 0 = ((π : ↥K.1) : Om l) → (∀ n, y (n + 1) ^ l = y n) → (∀ n, z (n + 1) ^ l = z n) → ∃ g : ↥(GK K), ∀ n, (g : GQ l) (y n) = z n := by
  intro l _ K π hπ y z hy hz hy' hz'
  have hGK : IsClosed ((GK K : Subgroup (GQ l)) : Set (GQ l)) := by
    unfold GK
    exact InfiniteGalois.fixingSubgroup_isClosed _

  have hpow : ∀ w : ℕ → Om l, (∀ n, w (n + 1) ^ l = w n) → ∀ m k, w (m + k) ^ (l ^ k) = w m := by
    intro w hw m k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul', ← add_assoc, hw, ih]

  let T : ℕ → Set (GQ l) := fun n =>
    (GK K : Set (GQ l)) ∩ ⋂ m, ⋂ (_ : m ≤ n), {g : GQ l | g (y m) = z m}
  have hcl : ∀ n, IsClosed (T n) := fun n =>
    hGK.inter (isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_setOf_gal_apply_eq_padic l (y m) (z m))
  have hdec : ∀ n, T (n + 1) ⊆ T n := by
    rintro n g ⟨h1, h2⟩
    refine ⟨h1, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    exact Set.mem_iInter.1 (Set.mem_iInter.1 h2 m) (Nat.le_succ_of_le hm)
  have hne : ∀ n, (T n).Nonempty := by
    intro n
    have hyn : y n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow y hy' 0 n
      rw [zero_add] at h
      rw [h, hy]
    have hzn : z n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow z hz' 0 n
      rw [zero_add] at h
      rw [h, hz]
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_apply_eq_of_pow_eq_prime l K π hπ (l ^ n) (y n) (z n) hyn hzn
      (pow_pos (Fact.out : l.Prime).pos n)
    refine ⟨(g : GQ l), g.2, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    show (g : GQ l) (y m) = z m
    rw [← hpow y hy' m k, ← hpow z hz' m k, map_pow, hg]

  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  refine ⟨⟨g, (Set.mem_iInter.1 hg 0).1⟩, fun n => ?_⟩
  exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hg n).2 n) le_rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesPair
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.PairFormula

theorem perp_iff {n : ℕ} [NeZero n] {Λ : Type} [CommRing Λ]
    {M : Type} [AddCommGroup M] [Module Λ M] [Module (ZMod n) M] [TopologicalSpace M]
    [DiscreteTopology M]
    {M' : Type} [AddCommGroup M'] [Module Λ M'] [TopologicalSpace M'] [DiscreteTopology M']
    {D Γ : Type} [Group D] [TopologicalSpace D] [Group Γ]
    (ρ : Representation Λ D M) (ρ' : Representation Λ D M') (P : M →+ M' →+ ZMod n)
    (μ : Γ →* (ZMod n)ˣ) (ρS : Representation (ZMod n) Γ M) (φ : D →* Γ)
    (hρ : ∀ g m, ρ g m = ρS (φ g) m) (hc : ContAction (ρS.comp φ)) (χ : D → ZMod n)
    (hχ : ∀ g, χ g = ((μ (φ g) : (ZMod n)ˣ) : ZMod n))
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y)
    (L : Submodule Λ (H1 ρ)) (LS : Submodule (ZMod n) (H1 (ρS.comp φ)))
    (hL : ∀ (z : Z1 ρ) (z' : Z1 (ρS.comp φ)), (∀ g, z'.1 g = z.1 g) →
      (Submodule.Quotient.mk z ∈ L ↔ Submodule.Quotient.mk z' ∈ LS))
    (y : Z1 ρ') (y' : Z1 ((twDual μ ρS).comp φ)) (hy : ∀ g x, y'.1 g x = P x (y.1 g)) :
    (∀ x ∈ LS, cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') x = 0) ↔
      ∀ x : Z1 ρ, Submodule.Quotient.mk x ∈ L → CupB χ (fun g m => ρ' g m) P x.1 y.1 := by
  let E := GlobalTheory.DualPairFormula.cocycleEquiv ρ (ρS.comp φ) (AddEquiv.refl M) hρ
  have hE : ∀ x g, (E x).1 g = x.1 g := fun _ _ => rfl
  have key : ∀ (x : Z1 ρ) g h, P (x.1 (g * h)) (y.1 (g * h)) = P (x.1 g) (y.1 g) +
      P (x.1 g) (ρ' g (y.1 h)) + P (ρ g (x.1 h)) (y.1 g) + χ g * P (x.1 h) (y.1 h) :=
    fun x g h => by
    rw [x.2.2, y.2.2, ← hP]
    simp only [map_add (f := _), AddMonoidHom.add_apply]
    ring
  have cb : ∀ x : Z1 ρ, Continuous fun g => P (x.1 g) (y.1 g) := fun x =>
    (continuous_of_discreteTopology (f := fun p : M × M' => P p.1 p.2)).comp
      (x.2.1.prodMk y.2.1)
  have hcup : ∀ x : Z1 ρ,
      cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        P (x.1 g) (ρ' g (y.1 h)) = χ g * c h - c (g * h) + c g := fun x => by
    have e0 : cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        χ g * c h - c (g * h) + c g = P (ρ g (x.1 h)) (y.1 g) := by
      refine (Submodule.Quotient.mk_eq_zero _).trans ((separated_dvr_second_cohomology_mem _ _).trans ?_)
      refine exists_congr fun c => and_congr_right fun _ => ?_
      rw [funext_iff, Prod.forall]
      refine forall_congr' fun g => forall_congr' fun h => ?_
      rw [← hy, hρ, hχ]
      exact Iff.rfl
    rw [e0]
    constructor
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - P (x.1 g) (y.1 g), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h - key x g h
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - P (x.1 g) (y.1 g), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h + key x g h
  constructor
  · intro H x hx
    obtain ⟨c, hc1, hc2⟩ := (hcup x).1 (H _ ((hL _ _ (hE _)).1 hx))
    exact ⟨c, (IsLocallyConstant.iff_continuous c).2 hc1, hc2⟩
  · intro H x hx
    induction x using Submodule.Quotient.induction_on with | H x =>
    obtain ⟨x, rfl⟩ := E.surjective x
    obtain ⟨f, hf1, hf2⟩ := H x ((hL _ _ (hE _)).2 hx)
    exact (hcup x).2 ⟨f, hf1.continuous, hf2⟩


open GlobalTheory.DualPairFormula GlobalTheory.SelInf in
theorem greenbergWiles_pair : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1) → ∀ (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ C : Set (H1 ρ'), (∀ y : Z1 ρ', Submodule.Quotient.mk y ∈ C ↔ (∀ v ∉ S, ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧ ∀ v ∈ S, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) → Finite C ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card W ^ InfinitePlace.nrComplexPlaces F = Nat.card C * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ n Λ _ W _ _ _ _ _ W' _ _ _ _ _ ρ ρ' P hn hρ hρ' h1 h2 hP
    S A hS hur L hL C hC
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hk : ∀ (x : W) (y : W'), (l ^ n) • P x y = 0 := fun x y => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  haveI : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => h1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, hk]
  haveI : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => h2 _ fun x => by
    rw [map_nsmul, hk]
  obtain ⟨ρS, hρS, hd⟩ := exists_descent (zmodRep (l ^ n) ρ) hρ (S : Set _)
    fun v hv B hB σ hσ => by
      ext x
      change ρ σ x = x
      rw [(hur v hv B hB σ hσ).1]
      rfl
  replace hd : ∀ (g : G F Ω) (x : W), ρ g x = ρS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g) x := hd
  obtain ⟨μ, hμ⟩ := PoitouTate.exists_lift_cycMod (Ω := Ω) (r := n) hS
  have hμ' : ∀ g, ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) =
      ((μ (toGS Ω _ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := fun g => by rw [← hμ]; rfl
  have hfin : Finite (TDual (ZMod (l ^ n)) W) := GlobalTheory.DualSide.finite_TDual
  have hfin' : Finite (TDual (ZMod (l ^ n)) W') := GlobalTheory.DualSide.finite_TDual
  let f : W' →+ TDual (ZMod (l ^ n)) W := AddMonoidHom.mk'
    (fun y => TDual.mk ((P.flip y).toZModLinearMap (l ^ n))) (fun y y' => by refine DFunLike.ext _ _ fun x => ?_; simp)
  have hf : ∀ y x, f y x = P x y := fun _ _ => rfl
  have inj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ?_
    rw [← hf, hy]
    rfl
  have c1 : Nat.card (TDual (ZMod (l ^ n)) W) = Nat.card W := GlobalTheory.ZModDual.card_dual_eq _ W
  have c2 : Nat.card (TDual (ZMod (l ^ n)) W') = Nat.card W' := GlobalTheory.ZModDual.card_dual_eq _ W'
  have c3 : Nat.card W ≤ Nat.card W' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective
      (fun x => TDual.mk ((P x).toZModLinearMap (l ^ n))) fun x x' hxx' => ?_
    have : ∀ y, P x y = P x' y := fun y =>
      congrArg (fun φ : TDual (ZMod (l ^ n)) W' => φ y) hxx'
    exact sub_eq_zero.1 (h1 _ fun y => by rw [map_sub, AddMonoidHom.sub_apply, this, sub_self])
  let e : W' ≃+ TDual (ZMod (l ^ n)) W :=
    AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3))
  have he : ∀ y x, e y x = P x y := fun _ _ => rfl
  have hee : ∀ g y, e (ρ' g y) = twDual μ ρS (toGS Ω _ g) (e y) := fun g y => by
    refine DFunLike.ext _ _ fun x => ?_
    rw [twDual_apply, he, he, ← map_inv, ← hd, ← hμ', ← hP, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  have hex := fun v : S => exists_transport_cond (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
    (ρS.comp (locFam S (fun v => A.1 v.1) v)) (AddEquiv.refl W) (fun g x => hd g x) (L v.1)
  choose LS hLS1 hLS2 using hex
  obtain ⟨f1, f2, hmain⟩ := GlobalTheory.GWComplex.greenbergWiles_totallyComplex hPT hLF hGF hEC F Ω l n W S
    ρS hn hS hρS μ hμ (fun v => A.1 v.1) (fun v => A.2 v.1) LS
  obtain ⟨E1⟩ := selAll_equiv_sel F Ω Λ (ZMod (l ^ n)) W W S A ρ ρS (AddEquiv.refl W) hρ hd L LS
    hL hLS2

  have hv' : ∀ (z : Z1 (twDual μ ρS)) (v : S),
      resH1 (twDual μ ρS) (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v)
        (Submodule.Quotient.mk z) ∈ perpCond μ ρS (locFam S fun v => A.1 v.1)
          (fun v => hρS.comp' (continuous_locFam S _ v)) LS v ↔
      ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v.1)).subtype), Submodule.Quotient.mk x ∈ L v.1 →
        CupB (fun g : Dec (F := F) (A.1 v.1) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
          (fun g m => ρ' g.1 m) P x.1 (fun g => (infZ e hee z).1 g.1) := fun z v => by
    rw [mem_perpCond]
    exact perp_iff (ρ.comp (Dec (F := F) (A.1 v.1)).subtype) (ρ'.comp (Dec (F := F) (A.1 v.1)).subtype)
      P μ ρS (locFam S (fun v => A.1 v.1) v) (fun g x => hd g x) _
      (fun g => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g => hμ' g.1)
      (fun g => hP g.1) (L v.1) (LS v) (hLS2 v)
      (restrictCocycles1 ρ' (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (infZ e hee z))
      (restrictCocycles1 (twDual μ ρS) (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) z)
      (fun g x => by
        change z.1 (toGS Ω _ g.1) x = P x (e.symm (z.1 (toGS Ω _ g.1)))
        rw [← he, e.apply_symm_apply])
  have hmem : ∀ z : Z1 (twDual μ ρS),
      Submodule.Quotient.mk z ∈ Sel (twDual μ ρS) (locFam S fun v => A.1 v.1) (continuous_locFam S _)
        (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) ↔
      Submodule.Quotient.mk (infZ e hee z) ∈ C := fun z => by
    rw [mem_Sel, hC]
    constructor
    · intro h
      refine ⟨fun v hv σ hσ => ?_, fun v hv x hx => (hv' z ⟨v, hv⟩).1 (h ⟨v, hv⟩) x hx⟩
      have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) σ = 1 :=
        (QuotientGroup.eq_one_iff σ).2 (Ine_le_NS (by simpa using hv) (A.2 v) hσ)
      rw [infZ_apply, this, z_one, map_zero]
    · rintro ⟨-, h⟩ v
      exact (hv' z v).2 (h v.1 v.2)
  have hmem' : ∀ x : H1 (twDual μ ρS),
      x ∈ Sel (twDual μ ρS) (locFam S fun v => A.1 v.1) (continuous_locFam S _)
        (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) ↔
      infH e hee x ∈ C := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [infH_mk]
    exact hmem z
  let T := Equiv.ofBijective (fun x : Sel (twDual μ ρS) (locFam S fun v => A.1 v.1)
      (continuous_locFam S _) (perpCond μ ρS (locFam S fun v => A.1 v.1)
        (fun v => hρS.comp' (continuous_locFam S _ v)) LS) =>
      (⟨infH e hee x.1, (hmem' _).1 x.2⟩ : C)) ⟨fun x y h => ?_, fun y => ?_⟩
  · have hs : Function.Surjective (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) :=
      QuotientGroup.mk'_surjective _
    refine ⟨Finite.of_equiv _ T, ?_⟩
    rw [Nat.card_congr E1, ← Nat.card_congr T, ← card_H0_eq_of_equivariant_equiv ρ' _ _ hs e hee,
      ← card_H0_eq_of_equivariant_equiv ρ ρS _ hs (AddEquiv.refl W) hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort S]
    simp only [← hLS1]
    rw [← hmain]
    congr 2
    refine Finset.prod_congr rfl fun v _ => ?_
    exact (card_H0_eq_of_equivariant_equiv (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
      (ρS.comp (locFam S (fun v => A.1 v.1) v)) id Function.surjective_id (AddEquiv.refl W)
      (fun g x => hd g x)).symm
  · exact Subtype.ext (infH_injective e hee (congrArg Subtype.val h))
  · obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z', rfl⟩ := exists_infZ e hee z (vanish_NS e hee A z ((hC z).1 hy).1)
    exact ⟨⟨Submodule.Quotient.mk z', (hmem' _).2 (by rw [infH_mk]; exact hy)⟩,
      Subtype.ext (infH_mk e hee z')⟩

end GlobalTheory.PairFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeAdaptedBasisGaloisActionBdRPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalAdapted

theorem gal_V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → (ρ g).map ((aDp l).comp (Per.zA l)) * H.V.map (Per.σDp (g : GQ l)) * Matrix.diagonal (fun j => aDp l w ^ H.p j) = aDp l w ^ H.q • H.V := by
  intro l _ K bk C d ρ H g w hw
  have hinj : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := (BdRField.bdR_isField l).2.1
  obtain ⟨u, hu, -⟩ := AdaptedHodge.xi_unit_fil C (bk.ev bk.E) bk.span_ev
  have hΞ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E))) := hu ▸ u.isUnit
  have hξ : Per.σD (g : GQ l) (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) := by
    rw [ActLaws.σD_alg, ActLaws.σDp_aDp, hw, map_mul, map_mul]
  have hmap : ∀ z : ℤ_[l], C.o (zOm l z) = aDp l (Per.zA l z) := fun z => C.o_sec.z z
  have hinv := H.inv g g.2
  ext i j
  apply hinj
  refine (hΞ.pow (H.p j)).mul_left_cancel ?_
  have hσ : ∀ k, (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w)) ^ H.q *
      Per.σD (g : GQ l) (H.Q k j) = (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w)) ^ H.p j *
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp (g : GQ l) (H.V k j)) := by
    intro k
    have := congrArg (Per.σD (g : GQ l)) (H.Q_eq k j)
    rw [map_mul, map_pow, hξ, ActLaws.σD_alg, map_mul, map_pow, ActLaws.σDp_aDp, hw, map_mul, map_mul, map_pow, map_mul] at this
    rw [this]
  have hI : ∑ k, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (ρ g i k))) * Per.σD (g : GQ l) (H.Q k j) = H.Q i j := by
    have := congrFun (congrFun hinv i) j
    simpa [Matrix.mul_apply, hmap] using this
  rw [Matrix.mul_diagonal, Matrix.smul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, RingHom.comp_apply,
    map_mul, map_sum, map_pow]
  have e1 : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j *
      (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (H.V i j)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) ^ H.q *
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * H.Q i j) := by
    rw [H.Q_eq i j, map_mul, map_pow]; ring
  rw [e1, ← hI]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination -(algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (ρ g i k)))) * hσ k

end GlobalTheory.BKLim.GalAdapted
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeAdaptedBasisInvariantMatrixRatio
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.InvRatio

theorem fixed_of_inv {A : Type} [CommRing A] {d : ℕ} (σ : A →+* A) (R Q Q' c : Matrix (Fin d) (Fin d) A)
    (hQu : IsUnit Q) (hc : Q * c = Q') (h1 : R * Q.map σ = Q) (h2 : R * Q'.map σ = Q') : c.map σ = c := by
  have e : Q'.map σ = Q.map σ * c.map σ := by rw [← hc, Matrix.map_mul]
  have : Q * c.map σ = Q * c := by
    rw [hc, ← h1, Matrix.mul_assoc, ← e, h2]
  exact hQu.mul_left_cancel this

end GlobalTheory.BKLim.InvRatio


open GlobalTheory.BKLim.InvRatio in
theorem GlobalTheory.BKLim.invMatrix_ratio : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit Q → (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q) → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, ∃ c c' : Matrix (Fin d) (Fin d) (Om l), (∀ i j, c i j ∈ K.1) ∧ (∀ i j, c' i j ∈ K.1) ∧ c * c' = 1 ∧ H.Q = Q * c.map C.oD := by
  intro l _ K bk C hI d ρ Q hQu hQ H
  obtain ⟨-, hinj, hF, -⟩ := BdRField.bdR_isField l
  obtain ⟨u, hu, -⟩ := AdaptedHodge.xi_unit_fil C (bk.ev bk.E) bk.span_ev
  set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι

  have hz : ∀ z : ℤ_[l], ι (C.o (zOm l z)) = Per.zD l z := by
    intro z
    simp only [zOm, RingHom.comp_apply, hι]
    exact (congrArg ι (C.o_sec.z z)).trans (GlobalTheory.RingIface.zD_eq_alg l z).symm
  have hHinv : ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * H.Q.map (Per.σD (g : GQ l)) = H.Q := by
    intro g
    have h := H.inv g g.2
    have e : ((ρ g).map (zOm l)).map (ι.comp C.o) = (ρ g).map (Per.zD l) := by
      ext i j; simp [hz]
    rwa [e] at h

  set dg : Fin d → Per.BdR l := fun k => ((u⁻¹ ^ H.q : (Per.BdR l)ˣ) : Per.BdR l) * (u : Per.BdR l) ^ H.p k with hdg
  have hQH : H.Q = H.V.map ι * Matrix.diagonal dg := by
    ext i k
    rw [Matrix.mul_diagonal, Matrix.map_apply]
    have h := H.Q_eq i k
    rw [map_mul, map_pow, ← hι, ← hu] at h
    calc H.Q i k = ((u⁻¹ ^ H.q : (Per.BdR l)ˣ) : Per.BdR l) * ((u : Per.BdR l) ^ H.q * H.Q i k) := by
          rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, one_mul]
      _ = ι (H.V i k) * dg k := by rw [h, hdg]; ring
  have hHu : IsUnit H.Q := by
    rw [hQH]
    refine IsUnit.mul ?_ ?_
    · exact H.unit.map (ι.mapMatrix)
    · rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
      intro k
      exact (Units.isUnit _).mul ((Units.isUnit u).pow _)

  obtain ⟨Qi, hQi⟩ : ∃ Qi, Q * Qi = 1 := ⟨_, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)⟩
  obtain ⟨Hi, hHi⟩ : ∃ Hi, H.Q * Hi = 1 := ⟨_, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHu)⟩
  set c₀ := Qi * H.Q with hc₀
  set c₀' := Hi * Q with hc₀'
  have e0 : Q * c₀ = H.Q := by rw [hc₀, ← Matrix.mul_assoc, hQi, Matrix.one_mul]
  have e0' : H.Q * c₀' = Q := by rw [hc₀', ← Matrix.mul_assoc, hHi, Matrix.one_mul]
  have fix0 : ∀ g ∈ GK K, ∀ i j, Per.σD g (c₀ i j) = c₀ i j := by
    intro g hg i j
    have := fixed_of_inv (Per.σD g) _ Q H.Q c₀ hQu e0 (hQ ⟨g, hg⟩) (hHinv ⟨g, hg⟩)
    exact congrFun (congrFun this i) j
  have fix0' : ∀ g ∈ GK K, ∀ i j, Per.σD g (c₀' i j) = c₀' i j := by
    intro g hg i j
    have := fixed_of_inv (Per.σD g) _ H.Q Q c₀' hHu e0' (hHinv ⟨g, hg⟩) (hQ ⟨g, hg⟩)
    exact congrFun (congrFun this i) j
  choose x hxK hx using fun i j => hI K (c₀ i j) (fun g hg => fix0 g hg i j)
  choose x' hxK' hx' using fun i j => hI K (c₀' i j) (fun g hg => fix0' g hg i j)
  haveI : Nontrivial (Per.BdR l) := hF.nontrivial
  have hoinj : Function.Injective C.oD := C.oD.injective
  have hm : (Matrix.of x).map C.oD = c₀ := by ext i j; simp [hx]
  have hm' : (Matrix.of x').map C.oD = c₀' := by ext i j; simp [hx']
  refine ⟨Matrix.of x, Matrix.of x', hxK, hxK', ?_, ?_⟩
  · have h1 : c₀ * c₀' = 1 := by
      rw [hc₀, hc₀', Matrix.mul_assoc, ← Matrix.mul_assoc H.Q, hHi, Matrix.one_mul]
      exact mul_eq_one_comm.1 hQi
    have h2 : (Matrix.of x * Matrix.of x').map C.oD = (1 : Matrix (Fin d) (Fin d) (Om l)).map C.oD := by
      rw [Matrix.map_mul, hm, hm', h1, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j
    exact hoinj (congrFun (congrFun h2 i) j)
  · rw [hm, e0]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpRestrictFiniteExt
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.JumpRestrict

open GlobalTheory.DRFil

theorem jump_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (hle : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (τ' : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ' a → IsJumpV (P.PD K) ρ (τ'.comp (IntermediateField.inclusion hle)) a := by
  intro l _ P AI T K K' LL hle V _ _ _ _ _ ρ hc τ' a hj
  have := K.2
  have := K'.2
  have := LL.2
  set τ := τ'.comp (IntermediateField.inclusion hle) with hτ
  have hF := isField_dR T
  haveI := (_root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  obtain ⟨m, d, k, hA⟩ := exists_adapted (P.PD K) hF ρ (filSpans T K LL ρ (crys T K LL ρ hc).1) τ
  set e' := idem (K := ↥K'.1) P.R.BdR (LL := ↥LL.1) τ' with he'
  set e := idem (K := ↥K.1) P.R.BdR (LL := ↥LL.1) τ with he
  have hee : e' * e = e' := by
    obtain ⟨n, x, c, hc1, hc2⟩ := idem_repr (K := ↥K.1) P.R.BdR τ
    rw [he, hc1]
    have := exists_smul_idem (K := ↥K'.1) (F := P.R.BdR) τ' n x (fun i => IntermediateField.inclusion hle (c i))
    exact (this.trans (by rw [← hc2]; rfl)).trans (one_smul _ _)
  have hA' : Adapted (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ'
      (fun i => sm ℚ_[l] P.R.BdR ↥LL.1 V e' (d i)) k := by
    refine ⟨fun i => ⟨?_, ?_⟩, fun r hr i => ?_, fun n y hy => ?_⟩
    · exact sm_idem_mem_DdRE (P.PD K') _ τ' (GlobalTheory.Per.TiedRestrict.ddR_le hle ρ (hA.mem i).1.1)
    · refine sm_idem_mem_FilV (P.PD K') τ' ?_
      rw [GlobalTheory.JumpDescent.FilV_eq P K K']
      exact (hA.mem i).2
    · have h1 := hA.indep (fun i => r i * e') (by
        rw [← hr]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_mul])
      calc e' * r i = (e' * e) * r i := by rw [hee]
        _ = e * (r i * e') := by ring
        _ = 0 := h1 i
    · rw [GlobalTheory.JumpDescent.FilV_eq P K K'] at hy
      obtain ⟨r, hr, hy'⟩ := hA.span n y hy
      refine ⟨r, fun i => ?_, ?_⟩
      · rw [GlobalTheory.JumpDescent.FilV_eq P K K']
        exact hr i
      · have h2 : sm ℚ_[l] P.R.BdR ↥LL.1 V e' y =
            sm ℚ_[l] P.R.BdR ↥LL.1 V e' (sm ℚ_[l] P.R.BdR ↥LL.1 V e y) := by
          rw [← sm_mul, hee]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [h2, hy', map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_comm]
  rw [hA'.isJumpV_iff] at hj
  exact hA.isJumpV_iff a |>.2 hj

end GlobalTheory.Per.JumpRestrict
end

