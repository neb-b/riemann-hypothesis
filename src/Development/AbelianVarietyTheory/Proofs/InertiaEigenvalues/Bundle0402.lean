module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0380
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityPerfectPairFiniteModules
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.LocalPair

theorem exists_dual_equiv {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [Finite M'] (P : M →+ M' →+ ZMod n)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    ∃ e : M' ≃+ TDual (ZMod n) M, ∀ y x, e y x = P x y := by
  let f : M' →+ TDual (ZMod n) M := AddMonoidHom.mk'
    (fun y => TDual.mk ((P.flip y).toZModLinearMap n)) (fun y y' => by refine DFunLike.ext _ _ fun x => ?_; simp)
  have hf : ∀ y x, f y x = P x y := fun _ _ => rfl
  have inj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ?_
    rw [← hf, hy]
    rfl
  have c1 : Nat.card (TDual (ZMod n) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq n M
  have : Finite (TDual (ZMod n) M) := Nat.finite_of_card_ne_zero (by rw [c1]; exact Nat.card_pos.ne')
  have c2 : Nat.card (Module.Dual (ZMod n) M') = Nat.card M' := GlobalTheory.ZModDual.card_dual_eq n M'
  have : Finite (Module.Dual (ZMod n) M') := Nat.finite_of_card_ne_zero (by rw [c2]; exact Nat.card_pos.ne')
  have c3 : Nat.card M ≤ Nat.card M' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective (fun x => ((P x).toZModLinearMap n : Module.Dual (ZMod n) M')) ?_
    intro x x' hx
    rw [← sub_eq_zero]
    refine h1 _ fun y => ?_
    rw [map_sub, AddMonoidHom.sub_apply, sub_eq_zero]
    exact DFunLike.congr_fun hx y
  exact ⟨AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3)), hf⟩

theorem dual_equivariant {n : ℕ} {Λ D : Type} [CommRing Λ] [Group D]
    {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Module Λ M] {M' : Type} [AddCommGroup M'] [Module Λ M']
    (ρ : Representation Λ D M) (ρ' : Representation Λ D M') (P : M →+ M' →+ ZMod n) (χ : D →* (ZMod n)ˣ)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = (χ g : ZMod n) * P x y) (e : M' ≃+ TDual (ZMod n) M)
    (he : ∀ y x, e y x = P x y) (g : D) (y : M') : e (ρ' g y) = twDual χ (zmodRep n ρ) g (e y) := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [twDual_apply, he, he]
  change _ = _ * P (ρ g⁻¹ x) y
  rw [← hP, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {D : Type} [Group D] [TopologicalSpace D]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  (ρ : Representation R D M) (ρ' : Representation R' D M') (e : M ≃+ M')
  (he : ∀ g m, e (ρ g m) = ρ' g (e m))

private def cocycleTransport : Z1 ρ ≃+ Z1 ρ' where
  toFun z := ⟨fun g => e (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add (f := _), he]⟩
  invFun z := ⟨fun g => e.symm (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    apply e.injective
    rw [map_add (f := _), he]
    simp only [AddEquiv.apply_symm_apply]
    exact z.2.2 g h⟩
  left_inv z := Subtype.ext (funext fun g => e.symm_apply_apply _)
  right_inv z := Subtype.ext (funext fun g => e.apply_symm_apply _)
  map_add' z w := Subtype.ext (funext fun g => map_add e _ _)


include he in
private theorem exists_H1_transport : ∃ T : H1 ρ ≃+ H1 ρ', ∀ (z : Z1 ρ) (z' : Z1 ρ'),
    (∀ g, z'.1 g = e (z.1 g)) → T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  refine ⟨QuotientAddGroup.congr ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup
    ((B1 ρ').comap (Z1 ρ').subtype).toAddSubgroup (cocycleTransport ρ ρ' e he) ?_, fun z z' h => ?_⟩
  · ext z'
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 hz
      refine (mem_coboundaries1 ρ' _).2 ⟨e m, fun g => ?_⟩
      change e (z.1 g) = _
      rw [← he, ← map_sub]
      exact congrArg e (hm g)
    · intro hz
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 hz
      refine ⟨(cocycleTransport ρ ρ' e he).symm z', (mem_coboundaries1 ρ _).2 ⟨e.symm m, fun g => ?_⟩,
        (cocycleTransport ρ ρ' e he).apply_symm_apply z'⟩
      apply e.injective
      change e (e.symm (z'.1 g)) = _
      rw [map_sub, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hm g
  · obtain rfl : z' = cocycleTransport ρ ρ' e he z := Subtype.ext (funext h)
    rfl

end Transport

private theorem card_H0_transport {R R' : Type} [CommRing R] [CommRing R'] {D D' : Type} [Group D] [Group D']
    {M : Type} [AddCommGroup M] [Module R M] {M' : Type} [AddCommGroup M'] [Module R' M']
    (ρ : Representation R D M) (ρ' : Representation R' D' M') (φ : D → D')
    (hφ : Function.Surjective φ) (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρ' (φ g) (e m)) :
    Nat.card (H0 ρ') = Nat.card (H0 ρ) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_)).symm
  change (∀ g, ρ g m = m) ↔ ∀ g, ρ' g (e m) = e m
  rw [hφ.forall]
  refine forall_congr' fun g => ?_
  rw [← he, e.injective.eq_iff]

theorem local_pair : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (Dec (F := F) A) W) (ρ' : Representation Λ (Dec (F := F) A) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → (∀ y : Z1 ρ', (∀ x : Z1 ρ, CupB (fun g : Dec (F := F) A => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g m) P x.1 y.1) ↔ Cob ρ' y.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H0 ρ')) := by
  intro hLF hLD hLE F Ω _ _ _ _ _ l _ n A v hA Λ _ W _ _ _ _ _ W' _ _ _ _ _ ρ ρ' P hn hρ hρ' h1 h2 hP
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => h1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => h2 _ fun x => by
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let χ := (cycMod F Ω l n).comp (Dec (F := F) A).subtype
  refine ⟨fun y => ⟨fun H => ?_, ?_⟩, fun hv => ?_⟩
  · obtain ⟨e, he⟩ := exists_dual_equiv P.flip h2 h1
    have hee := dual_equivariant ρ' ρ P.flip χ (fun g y x => hP g x y) e he
    have hinj := (hLD F Ω l n W' A (zmodRep (l ^ n) ρ') v hn hA hρ').2.2.2.1.1
    rw [injective_iff_map_eq_zero] at hinj
    let y' : Z1 ((zmodRep (l ^ n) ρ').comp (MonoidHom.id _)) := ⟨y.1, y.2.1, y.2.2⟩
    have h0 := hinj (Submodule.Quotient.mk y') (by
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with | H x =>
      obtain ⟨x, rfl⟩ := (cocycleTransport ρ ((twDual χ (zmodRep (l ^ n) ρ')).comp (MonoidHom.id _)) e hee).surjective x
      obtain ⟨f, hf1, hf2⟩ := H x
      refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨f, hf1.continuous, funext fun p => ?_⟩)
      exact (hf2 p.1 p.2).symm.trans (he _ _).symm)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩ x
    refine ⟨fun g => -P (x.1 g) (ρ' g m), (IsLocallyConstant.iff_continuous _).2 ?_, fun g h => ?_⟩
    · exact ((continuous_of_discreteTopology (f := fun p : W × W' => P p.1 p.2)).comp
        (x.2.1.prodMk (hρ'.comp (continuous_id.prodMk continuous_const)))).neg
    · beta_reduce
      rw [mul_neg, ← hP, x.2.2, hm, map_mul, Module.End.mul_apply]
      simp only [map_add (f := _), map_sub, AddMonoidHom.add_apply]
      ring
  · obtain ⟨e, he⟩ := exists_dual_equiv P h1 h2
    have hee := dual_equivariant ρ ρ' P χ hP e he
    obtain ⟨⟨j⟩, -, -, -, hb⟩ := hLD F Ω l n W A (zmodRep (l ^ n) ρ) v hn hA hρ
    have hE := (hLE F Ω l n W A (zmodRep (l ^ n) ρ) v hn hA hρ).2 hv
    obtain ⟨T, -⟩ := exists_H1_transport ρ (zmodRep (l ^ n) ρ) (AddEquiv.refl W) fun _ _ => rfl
    have c0 := card_H0_transport ρ (zmodRep (l ^ n) ρ) id Function.surjective_id (AddEquiv.refl W) fun _ _ => rfl
    have c0' := card_H0_transport ρ' ((twDual χ (zmodRep (l ^ n) ρ)).comp (MonoidHom.id _)) id Function.surjective_id e hee
    have : Finite (TDual (ZMod (l ^ n)) W) := Finite.of_equiv _ e.toEquiv
    rw [Nat.card_congr T.toEquiv, hE, c0, ← c0']
    congr 1
    refine (Nat.card_eq_of_bijective _ hb).trans ?_
    exact (Nat.card_congr (LinearEquiv.congrRight j).toEquiv).trans (GlobalTheory.ZModDual.card_dual_eq _ _)

end GlobalTheory.LocalPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInvariantsKilled
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.LocInv

theorem tors_of_finite (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (Y : Type) [AddCommGroup Y] [Module A Y] :
    Tors A Y := by
  intro b
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, fun x hx => ?_⟩
  rw [hn] at hx
  rw [(Submodule.mem_bot _).1 hx, zero_smul]

theorem dual_eq_one {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (h : IsotypicValuationAtRing bkP i s) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ)
    (v : PlE D.host) (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl i) (σ : GE N)
    (hσ : σ ∈ Ine (F := D.host.E) (N.plOm.1 v)) : ρ σ = 1 := by
  have hvl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := hl
  have h1 : cycZ D.host.E N.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hvl (N.plOm.2 v) (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  have h2 : eps0 X i σ = 1 := by
    rw [eps0, MonoidHom.comp_apply, h1, map_one]
  have h3 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s h v hl hS _ (N.plOm.2 v) σ hσ
  apply Units.ext
  rw [hρ σ, Tdual, h2, ← Tgl_coe, h3]
  simp

theorem local_invariants_killed : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (t : A) (a : Fin R ⊕ Fin n → A), IsQ P Q → Setup bkP i s κ Q → Kills i A → IsDual i s ρ → IsChar i κ (fun q => a q * t) (fun q => d (P q)) → (∀ q, IsUnit (a (.inr q))) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y], ∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y g m = m) → t • m = 0 := by
  intro _ D N X bkP i s _ M R n d A₀ L z P hM hz hL hSt A _ _ _ _ κ Q ρ t a hQ hSet _ hρ hch ha Y _ _ _ _ v hv m hm
  obtain ⟨hG, hloc, -, hκo, hκl, -, hQl, -⟩ := hSet
  have hκl' : ∀ g, ∃ k : ℕ, κ⁻¹ g ^ (X.l i ^ k) = 1 := fun g => by
    obtain ⟨k, hk⟩ := hκl g
    exact ⟨k, by rw [MonoidHom.inv_apply, inv_pow, hk, inv_one]⟩
  by_cases hS : v ∈ Spl i
  · have hker : (κ⁻¹).ker = κ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    have h0 := (GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s hG v hS A κ⁻¹ (hker ▸ hκo) hκl' Y
      (tors_of_finite A Y) ρ (Or.inr hρ)).1
    have : m ∈ H0 ((repOn ρ κ⁻¹ Y).comp (DecV N v).subtype) := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => hm g.1 g.2
    rw [h0, Submodule.mem_bot] at this
    rw [this, smul_zero]
  have hvQ : v ∈ Q := hv.resolve_left hS
  obtain ⟨q, hq⟩ := (hQ v).1 hvQ
  rcases q with b | q
  · have hA : ∀ w, Over (P (.inl b)) w → w ∉ X.S0 i ∧ normV w % X.l i = 1 := fun w hw => by
      obtain ⟨-, -, -, h0, -, hn⟩ := hSt.1.1 _ w hw
      exact ⟨h0, mod_l_eq_one i hM hn⟩
    have hp := hA v hq
    have hn := GlobalTheory.ScalarFrob.natCast_eq_one_of_mod i hp.2
    obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
    obtain ⟨c, c0, c1, hc⟩ := GlobalTheory.ScalarFrob.frob_scalar_place i s bkP hG hz hL.1 hA (hSt.2.1 b).2 hq hσ
    have hc' : ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) =
        c⁻¹ • 1 := by
      rw [hρ, GlobalTheory.ScalarFrob.dual_of_scalar i s (GlobalTheory.ScalarFrob.eps_frob i hp.1 hn hσ) c0 hc]
    rw [GlobalTheory.ScalarFrob.eq_zero_of_scalar Fact.out (GlobalTheory.PrimeToInertia.l_mem i) ρ κ⁻¹ (hκl' σ) (inv_ne_one.2 c1) hc'
      (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm σ hσ.1), smul_zero]
  · obtain ⟨γ, hγ, hd⟩ := (hSt.1.2.2 (.inr q)).2.2.2.2 v hq _ (N.plOm.2 v) (Multiplicative.ofAdd 1)
    have hρ1 := dual_eq_one bkP i s hG.1 hρ v (hQl v hvQ) hS γ hγ
    have hk := hch γ
    haveI : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) (Fact.out : (X.l i).Prime).one_lt⟩
    rw [Finset.prod_eq_single (Sum.inr q)] at hk
    · have hd' : d (P (.inr q)) γ = Multiplicative.ofAdd 1 := hd
      simp only [hd', toAdd_ofAdd, ZMod.val_one, pow_one] at hk
      have hinv : ((κ⁻¹ γ : Aˣ) : A) = 1 + a (.inr q) * t := by
        rw [MonoidHom.inv_apply]
        exact Units.inv_eq_of_mul_eq_one_right hk
      have e := hm γ (Ine_le_Dec _ hγ)
      have e2 : repOn ρ κ⁻¹ Y γ m = (1 + a (.inr q) * t) • m := by
        simp [repOn, hρ1, matAct_one, ← hinv]
      rw [e2, add_smul, one_smul, add_eq_left, mul_smul] at e
      exact ((ha q).smul_eq_zero).1 e
    · intro q' _ hne
      have hn : ¬ Over (P q') v := fun h' => hne (hSt.1.2.1 _ _ (over_trans h' (over_symm hq)))
      have : d (P q') γ = 1 := (hSt.1.2.2 q').2.2.2.1 v hn _ (N.plOm.2 v) γ hγ
      simp [this]
    · simp

end GlobalTheory.NewPrime.LocInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.ImageTower

variable {S A : Type} [CommRing S] [CommRing A] (e : S →+* A) (p : ℕ) {d : ℕ} {d' : ℕ → ℕ}
  (R : ∀ n, Matrix (Fin d) (Fin (d' n)) A)

def Img (n m : ℕ) : Set (Fin d → A) :=
  {w | ∃ s : Fin (d' m) → S, ∀ i, (p : A) ^ n ∣ (w - R m *ᵥ fun j => e (s j)) i}

variable {e p R}

theorem mem_of_dvd {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m)
    (h : ∀ i, (p : A) ^ n ∣ (x - w) i) : x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  refine ⟨s, fun i => ?_⟩
  have : (x - R m *ᵥ fun j => e (s j)) i = (x - w) i + (w - R m *ᵥ fun j => e (s j)) i := by
    simp only [Pi.sub_apply]; ring
  rw [this]; exact dvd_add (h i) (hs i)

theorem add_mem {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m) (hx : x ∈ Img e p R n m) :
    w + x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  obtain ⟨t, ht⟩ := hx
  refine ⟨s + t, fun i => ?_⟩
  have he : (fun j => e ((s + t) j)) = (fun j => e (s j)) + fun j => e (t j) := by
    funext j; simp
  rw [he, mulVec_add]
  have : (w + x - ((R m *ᵥ fun j => e (s j)) + R m *ᵥ fun j => e (t j))) i =
      (w - R m *ᵥ fun j => e (s j)) i + (x - R m *ᵥ fun j => e (t j)) i := by
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [this]; exact dvd_add (hs i) (ht i)

theorem image_mem (n m : ℕ) (s : Fin (d' m) → S) : (R m *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
  ⟨s, fun i => by simp⟩

theorem dvd_mulVec' {κ ι : Type} [Fintype ι] {q : A} (D : Matrix κ ι A) (h : ∀ i j, q ∣ D i j)
    (v : ι → A) (i : κ) : q ∣ (D *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _

theorem img_succ_sub (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m : ℕ} (hnm : n ≤ m) :
    Img e p R n (m + 1) ⊆ Img e p R n m := by
  rintro w ⟨s, hs⟩
  refine ⟨Y m *ᵥ s, fun i => ?_⟩
  have he : (fun j => e ((Y m *ᵥ s) j)) = (Y m).map e *ᵥ fun j => e (s j) := by
    funext j; exact RingHom.map_mulVec e (Y m) s j
  rw [he, mulVec_mulVec]
  have : (w - (R m * (Y m).map e) *ᵥ fun j => e (s j)) i =
      (w - R (m + 1) *ᵥ fun j => e (s j)) i -
        ((R m * (Y m).map e - R (m + 1)) *ᵥ fun j => e (s j)) i := by
    simp only [sub_mulVec, Pi.sub_apply]; ring
  rw [this]
  exact dvd_sub (hs i) ((pow_dvd_pow _ hnm).trans (dvd_mulVec' _ (h1 m) _ i))

theorem img_anti (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m m' : ℕ} (hnm : n ≤ m)
    (hm : m ≤ m') : Img e p R n m' ⊆ Img e p R n m := by
  induction m', hm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (img_succ_sub Y h1 (hnm.trans hk)).trans ih

theorem img_mod {k n m : ℕ} (hkn : k ≤ n) : Img e p R n m ⊆ Img e p R k m := by
  rintro w ⟨s, hs⟩; exact ⟨s, fun i => (pow_dvd_pow _ hkn).trans (hs i)⟩

theorem img_stable (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (n c : ℕ) [Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}))]
    (hc : ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := by
  let J : Ideal S := Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}
  let T : ℕ → Set (Fin (d' n) → S ⧸ J) := fun m =>
    {q | ∃ s : Fin (d' n) → S, (fun j => Ideal.Quotient.mk J (s j)) = q ∧
      (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m}
  have key : ∀ m m', n ≤ m → n ≤ m' → T m ⊆ T m' → Img e p R n m ⊆ Img e p R n m' := by
    intro m m' hm hm' hT w hw
    obtain ⟨s, hs⟩ := img_anti Y h1 le_rfl hm hw
    have hRs : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
      mem_of_dvd hw fun i => dvd_sub_comm.1 (hs i)
    obtain ⟨s', hq, hs'⟩ := hT ⟨s, rfl, hRs⟩
    have hj : ∀ j, ∃ a b : S, s j = s' j + (p : S) ^ n * a + u ^ c * b := by
      intro j
      have hqj : Ideal.Quotient.mk J (s' j) = Ideal.Quotient.mk J (s j) := congrFun hq j
      have hmem : s' j - s j ∈ J := Ideal.Quotient.eq.1 hqj
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hy
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 hz
      exact ⟨-a, -b, by linear_combination hyz⟩
    choose a b hab using hj
    obtain ⟨t, ht⟩ := hc m' hm' b
    have hsum : ((R n *ᵥ fun j => e (s' j)) + R n *ᵥ fun j => e (u ^ c * b j)) ∈ Img e p R n m' :=
      add_mem hs' (mem_of_dvd (image_mem n m' t) ht)
    have hRs' : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m' := by
      refine mem_of_dvd hsum fun i => ?_
      have hv : (fun j => e (s j)) = (fun j => e (s' j)) + (p : A) ^ n • (fun j => e (a j)) +
          fun j => e (u ^ c * b j) := by
        funext j; rw [hab j]; simp
      rw [hv, mulVec_add, mulVec_add, mulVec_smul]
      have : ((R n *ᵥ fun j => e (s' j)) + (p : A) ^ n • (R n *ᵥ fun j => e (a j)) +
          (R n *ᵥ fun j => e (u ^ c * b j)) - ((R n *ᵥ fun j => e (s' j)) +
            R n *ᵥ fun j => e (u ^ c * b j))) i = (p : A) ^ n * (R n *ᵥ fun j => e (a j)) i := by
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact dvd_mul_right _ _
    exact mem_of_dvd hRs' hs
  have hanti : Antitone fun k => T (n + k) := by
    rintro k k' hkk q ⟨s, rfl, hs⟩
    exact ⟨s, rfl, img_anti Y h1 (Nat.le_add_right n k) (by omega) hs⟩
  obtain ⟨k₀, hk₀⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨n + k₀, by omega, fun m hm => le_antisymm (img_anti Y h1 (by omega) hm) ?_⟩
  have hTe : T (n + k₀) = T m := by
    have := hk₀ (m - n) (by omega)
    rwa [Nat.add_sub_cancel' (by omega : n ≤ m)] at this
  exact key _ _ (by omega) (by omega) hTe.le

theorem ml (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (hfin : ∀ n c, Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c})))
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    (h2 : ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → S, ∃ v : Fin d → A,
      (∀ i, (p : A) ^ n ∣ (v - R m *ᵥ fun j => e (s j)) i) ∧
      ∀ k, ∃ s' : Fin (d' k) → S, ∀ i, (p : A) ^ k ∣ (v - R k *ᵥ fun j => e (s' j)) i := by
  have hst : ∀ n, ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := fun n => by
    obtain ⟨c, hc⟩ := h2 n
    haveI := hfin n c
    exact img_stable u Y h1 n c hc
  choose m₀ hnm₀ hm₀ using hst
  have lift : ∀ n x, x ∈ Img e p R n (m₀ n) →
      ∃ y, y ∈ Img e p R (n + 1) (m₀ (n + 1)) ∧ ∀ i, (p : A) ^ n ∣ (y - x) i := by
    intro n x hx
    rw [← hm₀ n (max (m₀ n) (m₀ (n + 1))) (le_max_left _ _)] at hx
    obtain ⟨s, hs⟩ := hx
    refine ⟨_, ?_, fun i => dvd_sub_comm.1 (hs i)⟩
    rw [← hm₀ (n + 1) (max (m₀ n) (m₀ (n + 1))) (le_max_right _ _)]
    exact image_mem _ _ s
  choose! L hL hLd using lift
  intro n
  refine ⟨m₀ n, hnm₀ n, fun s => ?_⟩
  set x₀ := R (m₀ n) *ᵥ fun j => e (s j) with hx₀def
  have hx₀ : x₀ ∈ Img e p R n (m₀ n) := image_mem _ _ s
  let w : ℕ → Fin d → A := fun k => Nat.rec x₀ (fun k y => L (n + k) y) k
  have hw0 : w 0 = x₀ := rfl
  have hws : ∀ k, w (k + 1) = L (n + k) (w k) := fun _ => rfl
  have hmem : ∀ k, w k ∈ Img e p R (n + k) (m₀ (n + k)) := by
    intro k; induction k with
    | zero => exact hx₀
    | succ k ih => rw [hws]; exact hL _ _ ih
  have htel : ∀ k j i, (p : A) ^ (n + k) ∣ (w (k + j) - w k) i := by
    intro k j; induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      have : (w (k + (j + 1)) - w k) i = (w (k + j + 1) - w (k + j)) i + (w (k + j) - w k) i := by
        rw [← add_assoc]; simp only [Pi.sub_apply]; ring
      rw [this, hws]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hLd _ _ (hmem _) i)) (ih i)
  have hcau : ∀ i, ∃ v : A, ∀ k, (p : A) ^ k ∣ w k i - v := by
    intro i
    obtain ⟨v, hv⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A) (f := fun k => w k i) (by
      intro a b hab
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
      have h' : (p : A) ^ a ∣ w (a + j) i - w a i := (pow_dvd_pow _ (by omega)).trans (htel a j i)
      exact dvd_sub_comm.1 h')
    refine ⟨v, fun k => ?_⟩
    have := hv k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at this
  choose V hV using hcau
  refine ⟨V, fun i => ?_, fun k => ?_⟩
  · have h1' := htel 0 n i
    rw [Nat.add_zero, Nat.zero_add, hw0] at h1'
    have : (V - x₀) i = (V i - w n i) + (w n - x₀) i := by simp only [Pi.sub_apply]; ring
    rw [this]; exact dvd_add (dvd_sub_comm.1 (hV i n)) h1'
  · have hk : w k ∈ Img e p R k k :=
      img_anti Y h1 le_rfl (le_trans (by omega) (hnm₀ (n + k))) (img_mod (by omega) (hmem k))
    exact mem_of_dvd hk fun i => dvd_sub_comm.1 (hV i k)

end GlobalTheory.ImageTower

theorem GlobalTheory.ImageTower.perfectRing_Cb' (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem GlobalTheory.BKLim.mittagLeffler_image : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) (bk.S)), (∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j) → (∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → bk.S, ∃ s' : Fin (d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i) → ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i := by
  intro l _ K bk d d' R Y h1 h2
  haveI : PerfectRing (Cb l) l := GlobalTheory.ImageTower.perfectRing_Cb' l
  haveI : IsAdicComplete (Ideal.span {(l : WCb l)}) (WCb l) := WittVector.isAdicCompleteIdealSpanP
  exact GlobalTheory.ImageTower.ml (e := bk.evW) (p := l) (R := R) X Y h1 (fun n c => _root_.GlobalTheory.BKFin.finite_quot l K bk n c) h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatInvIsoOfLocalTateDualityCyclotomicTwistStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.NatInvIso := by
  first | exact @GlobalTheory.natInvIso_of_localTateDuality | exact GlobalTheory.natInvIso_of_localTateDuality | (intros; apply GlobalTheory.natInvIso_of_localTateDuality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotDRLOfTied
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem potDRL_of_tied : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → PotDRL L := by
  intro L A hT l _ K K' LL h R hc
  obtain ⟨T⟩ := hT l
  exact (_root_.GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (L l) (A l) T K K' LL h R.V R.ρ).2.2
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (L l) (A l) T K' LL R.V _ hc).1

end GlobalTheory.Pass
end

