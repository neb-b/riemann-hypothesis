module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerFunctorLeftExactTorsionCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionOrderAboveLFiniteModules
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.LocCountFinite

theorem card_of_exact {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (h : Function.Exact f g) (hg : Function.Surjective g) : Nat.card B = Nat.card A * Nat.card C := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), Nat.card_congr (g.quotKerEquivOfSurjective hg).toEquiv,
    h.linearMap_ker_eq, ← Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv]

section Abstract

variable {R Γ M' M M'' : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup M''] [Module R M''] [TopologicalSpace M''] [DiscreteTopology M'']
  (ρ' : Representation R Γ M') (ρ : Representation R Γ M) (ρ'' : Representation R Γ M'')

abbrev coc (L : Submodule R (H1 ρ)) : Submodule R (Z1 ρ) := L.comap (Submodule.mkQ _)

theorem card_coc (hc : ContAction ρ) (L : Submodule R (H1 ρ)) :
    Nat.card (coc ρ L) * Nat.card (H0 ρ) = Nat.card L * Nat.card M := by
  let B := (B1 ρ).comap (Z1 ρ).subtype
  have hB : B ≤ coc ρ L := fun z hz => by
    have : (Submodule.Quotient.mk z : H1 ρ) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hz
    change (Submodule.Quotient.mk z : H1 ρ) ∈ L
    rw [this]; exact L.zero_mem
  have h1 : Nat.card (coc ρ L) = Nat.card B * Nat.card L := by
    refine card_of_exact (Submodule.inclusion hB) ((Submodule.mkQ B).restrict (p := coc ρ L) (q := L) fun _ h => h)
      (Submodule.inclusion_injective _) (fun z => ?_) (fun x => ?_)
    · constructor
      · intro hz
        exact ⟨⟨z.1, (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hz)⟩, rfl⟩
      · rintro ⟨b, rfl⟩
        exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 b.2)
    · obtain ⟨x, hx⟩ := x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨⟨z, hx⟩, rfl⟩
  have h2 : Nat.card M = Nat.card (H0 ρ) * Nat.card B := by
    refine card_of_exact (H0 ρ).subtype
      (((d0 ρ).codRestrict (Z1 ρ) fun m => coboundaries_le_cocycles ρ hc ⟨m, rfl⟩).codRestrict B fun m => ⟨m, rfl⟩)
      (Submodule.subtype_injective _) (fun m => ?_) (fun x => ?_)
    · constructor
      · intro hm
        refine ⟨⟨m, (mem_riemannRochSpace_iff_regularAt_everywhere ρ m).2 fun g => ?_⟩, rfl⟩
        have : ρ g m - m = 0 := congrFun (congrArg (fun z => z.1.1) hm) g
        exact sub_eq_zero.1 this
      · rintro ⟨b, rfl⟩
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        exact sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere ρ _).1 b.2 g)
    · obtain ⟨⟨z, hz⟩, m, hm⟩ := x
      exact ⟨m, Subtype.ext (Subtype.ext hm)⟩
  rw [h1, h2]; ring

theorem card_coc_mul (u : M' →ₗ[R] M) (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hinj : Function.Injective u)
    (w : M →ₗ[R] M'') (hw : ∀ g m, w (ρ g m) = ρ'' g (w m)) (hex : Function.Exact u w) (hsurj : Function.Surjective w)
    (hc : ContAction ρ) (L' : Submodule R (H1 ρ')) (L : Submodule R (H1 ρ)) (L'' : Submodule R (H1 ρ''))
    (h1 : ∀ x, mapH1 ρ' ρ u continuous_of_discreteTopology hu x ∈ L ↔ x ∈ L')
    (h2 : ∀ x ∈ L, mapH1 ρ ρ'' w continuous_of_discreteTopology hw x ∈ L'')
    (h3 : L'' ≤ L.map (mapH1 ρ ρ'' w continuous_of_discreteTopology hw)) :
    Nat.card (coc ρ L) = Nat.card (coc ρ' L') * Nat.card (coc ρ'' L'') := by
  refine card_of_exact
    ((cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu).restrict (p := coc ρ' L') (q := coc ρ L) fun z h => (h1 _).2 h)
    ((cocycles1MapOfEquivariant ρ ρ'' w continuous_of_discreteTopology hw).restrict (p := coc ρ L) (q := coc ρ'' L'') fun z h => h2 _ h)
    (fun a b h => Subtype.ext (Subtype.ext (funext fun g => hinj (congrFun (congrArg (fun z => z.1.1) h) g))))
    (fun z => ?_) (fun x => ?_)
  · constructor
    · intro hz
      have e1 : ∀ g, u (Function.invFun u (z.1.1 g)) = z.1.1 g := fun g =>
        Function.invFun_eq ((hex _).1 (congrFun (congrArg (fun z => z.1.1) hz) g))
      let z' : Z1 ρ' := ⟨fun g => Function.invFun u (z.1.1 g),
        (continuous_of_discreteTopology (f := Function.invFun u)).comp z.1.2.1, fun g h => hinj (by
          rw [map_add (f := _), hu, e1, e1, e1]
          exact z.1.2.2 g h)⟩
      have e : cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z' = z.1 := Subtype.ext (funext e1)
      refine ⟨⟨z', (h1 _).1 ?_⟩, Subtype.ext e⟩
      change Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z') ∈ L
      rw [e]; exact z.2
    · rintro ⟨b, rfl⟩
      exact Subtype.ext (Subtype.ext (funext fun g => hex.apply_apply_eq_zero _))
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy, e⟩ := h3 hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have e' : (Submodule.Quotient.mk (x - cocycles1MapOfEquivariant ρ ρ'' w continuous_of_discreteTopology hw z) : H1 ρ'') = 0 := by
      rw [Submodule.Quotient.mk_sub, sub_eq_zero]
      exact e.symm
    obtain ⟨m, hm⟩ := (GlobalTheory.SelLeftExact.mk_eq_zero_iff ρ'' _).1 e'
    obtain ⟨m, rfl⟩ := hsurj m
    let b : Z1 ρ := ⟨d0 ρ m, coboundaries_le_cocycles ρ hc ⟨m, rfl⟩⟩
    have hb : (Submodule.Quotient.mk b : H1 ρ) = 0 := (GlobalTheory.SelLeftExact.mk_eq_zero_iff ρ b).2 ⟨m, fun _ => rfl⟩
    refine ⟨⟨z + b, ?_⟩, Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    · change (Submodule.Quotient.mk (z + b) : H1 ρ) ∈ L
      rw [Submodule.Quotient.mk_add, hb, add_zero]
      exact hy
    · change w (z.1 g + (ρ g m - m)) = x.1 g
      have : x.1 g - w (z.1 g) = ρ'' g (w m) - w m := hm g
      rw [map_add (f := _), map_sub, hw, ← this]
      abel

theorem card_six [Finite M] (u : M' →ₗ[R] M) (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hinj : Function.Injective u)
    (w : M →ₗ[R] M'') (hw : ∀ g m, w (ρ g m) = ρ'' g (w m)) (hex : Function.Exact u w) (hsurj : Function.Surjective w)
    (hc' : ContAction ρ') (hc : ContAction ρ) (hc'' : ContAction ρ'')
    (L' : Submodule R (H1 ρ')) (L : Submodule R (H1 ρ)) (L'' : Submodule R (H1 ρ''))
    (h1 : ∀ x, mapH1 ρ' ρ u continuous_of_discreteTopology hu x ∈ L ↔ x ∈ L')
    (h2 : ∀ x ∈ L, mapH1 ρ ρ'' w continuous_of_discreteTopology hw x ∈ L'')
    (h3 : L'' ≤ L.map (mapH1 ρ ρ'' w continuous_of_discreteTopology hw)) :
    Nat.card L * (Nat.card (H0 ρ') * Nat.card (H0 ρ'')) = Nat.card (H0 ρ) * (Nat.card L' * Nat.card L'') := by
  have a := card_coc ρ hc L
  have a' := card_coc ρ' hc' L'
  have a'' := card_coc ρ'' hc'' L''
  have b := card_coc_mul ρ' ρ ρ'' u hu hinj w hw hex hsurj hc L' L L'' h1 h2 h3
  have c := card_of_exact u w hinj hex hsurj
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := M)) ?_
  calc _ = (Nat.card L * Nat.card M) * (Nat.card (H0 ρ') * Nat.card (H0 ρ'')) := by ring
    _ = Nat.card (H0 ρ) * ((Nat.card (coc ρ' L') * Nat.card (H0 ρ')) * (Nat.card (coc ρ'' L'') * Nat.card (H0 ρ''))) := by
      rw [← a, b]; ring
    _ = _ := by rw [a', a'', c]; ring

theorem contAction_sub (hc : ContAction ρ) (U : Subgroup Γ) : ContAction (ρ.comp U.subtype) :=
  hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

end Abstract

theorem tors_of_finite (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (B : Type) [AddCommGroup B] [Module A B] :
    Tors A B := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine fun b => ⟨n, fun x hx => ?_⟩
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

theorem finite_places (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l ≠ 0) : (placesOver F l).Finite := by
  have h : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    simpa using hl
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem locCountFin : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → LocSat bkP i s κ → LocCount bkP i s κ → LocCountFin bkP i s κ := by
  intro D N X bkP i s A _ _ _ _ κ Q hS hK hL hC Y _ _ _ _ _
  haveI := hS.2.1
  have hfin := finite_places D.host.E (X.l i) (Fact.out : (X.l i).Prime).ne_zero
  have hcont : ∀ (B : Type) [AddCommGroup B] [Module A B] [TopologicalSpace B] [DiscreteTopology B] (v : PlE D.host),
      ContAction ((repOn (Tgl i s) κ B).comp (DecV N v).subtype) := fun B _ _ _ _ v =>
    contAction_sub _ (GlobalTheory.SelLeftExact.contAction_of_tors (X.twistBaseCoefficientRing_isAdic i) _ (GlobalTheory.SelLeftExact.continuous_Tgl i s) κ
      hS.2.2.2.1 (tors_of_finite A B)) _
  induction hn : Nat.card Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
  subst hn
  rcases subsingleton_or_nontrivial Y with hY | hY
  · have e1 : ∀ v, Nat.card (bkOn bkP i (Tgl i s) κ Y v) = 1 := fun v => by
      haveI : Subsingleton (H1 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype)) :=
        (Submodule.Quotient.mk_surjective _).subsingleton
      exact Nat.card_unique
    have e2 : ∀ v, Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype)) = 1 := fun v => Nat.card_unique
    have e3 : Nat.card Y = 1 := Nat.card_unique
    simp only [e1, e2, e3, one_pow, mul_one]
  · obtain ⟨K, hKa, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule A Y)).resolve_left top_ne_bot
    have hKs : IsSimpleModule A K := isSimpleModule_iff_isAtom.2 hKa
    letI : TopologicalSpace (Y ⧸ K) := ⊥
    haveI : DiscreteTopology (Y ⧸ K) := ⟨rfl⟩
    haveI : Finite (Y ⧸ K) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective K)
    have hex : Function.Exact K.subtype K.mkQ := LinearMap.exact_subtype_mkQ K
    have hcard := card_of_exact K.subtype K.mkQ K.subtype_injective hex K.mkQ_surjective
    have hlt : Nat.card (Y ⧸ K) < Nat.card Y := by
      haveI := IsSimpleModule.nontrivial A K
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      have h2 : 0 < Nat.card (Y ⧸ K) := Nat.card_pos
      rw [hcard]
      nlinarith
    have a := hC K hKs
    have b := ih _ hlt (Y ⧸ K) rfl
    have c : ∀ v ∈ hfin.toFinset, Nat.card (bkOn bkP i (Tgl i s) κ Y v) *
        (Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype)) *
          Nat.card (H0 ((repOn (Tgl i s) κ (Y ⧸ K)).comp (DecV N v).subtype))) =
        Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype)) *
          (Nat.card (bkOn bkP i (Tgl i s) κ K v) * Nat.card (bkOn bkP i (Tgl i s) κ (Y ⧸ K) v)) := fun v hv => by
      have hv' := hfin.mem_toFinset.1 hv
      refine card_six _ _ _ (K.subtype.compLeft (Fin D.R.r)) (fun g m => repOn_map (Tgl i s) κ K.subtype g.1 m)
        (fun x y h => funext fun a => Subtype.ext (congrFun h a)) (K.mkQ.compLeft (Fin D.R.r))
        (fun g m => repOn_map (Tgl i s) κ K.mkQ g.1 m) (fun m => ⟨fun hm => ?_, ?_⟩) (fun m => ?_)
        (hcont _ v) (hcont _ v) (hcont _ v) _ _ _
        (fun x => ⟨hL v hv' K Y (tors_of_finite A Y) K.subtype K.subtype_injective x,
          localConditionAboveL_coeffMap_functorial bkP i _ κ K.subtype v x⟩)
        (localConditionAboveL_coeffMap_functorial bkP i _ κ K.mkQ v)
        (_root_.GlobalTheory.NewPrime.bkOn_le_map_of_surjective D N X bkP i s A κ Q hS hK Y (Y ⧸ K) K.mkQ K.mkQ_surjective v)
      · choose m' hm' using fun a => (hex (m a)).1 (congrFun hm a)
        exact ⟨m', funext hm'⟩
      · rintro ⟨m', rfl⟩
        exact funext fun a => hex.apply_apply_eq_zero _
      · choose m' hm' using fun a => K.mkQ_surjective (m a)
        exact ⟨m', funext hm'⟩
    have c' := Finset.prod_congr rfl c
    simp only [Finset.prod_mul_distrib] at c'
    simp only [finprod_mem_eq_finite_toFinset_prod _ hfin] at a b ⊢
    rw [a, b] at c'
    have hpos : 0 < (∏ v ∈ hfin.toFinset, Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype))) *
        ∏ v ∈ hfin.toFinset, Nat.card (H0 ((repOn (Tgl i s) κ (Y ⧸ K)).comp (DecV N v).subtype)) :=
      Nat.mul_pos (Finset.prod_pos fun v _ => Nat.card_pos) (Finset.prod_pos fun v _ => Nat.card_pos)
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [c', hcard, mul_pow]
    ring

end GlobalTheory.LocCountFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.DdREqDcris

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_mulVB (c : K₀) (d : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [mulVdR, ιV, mulVB, ← IsScalarTower.algebraMap_apply]

theorem act_mulVB (g : G) (c : K₀) (d : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [actVB, mulVB]

theorem mulVB_mem (c : K₀) {d : V ⊗[Qp] B} (hd : d ∈ Dcris PD ρ) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d ∈ Dcris PD ρ := by
  rw [CrisDR.mem_Dcris_iff] at hd ⊢
  intro g
  rw [act_mulVB, hd g]

theorem mulVdR_one (y : V ⊗[Qp] BdR) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) 1 y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [mulVdR]

theorem ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro d hd
  refine CrisDR.eq_zero_of_sum PD (LL := LL) (m := 1) (fun _ => (1 : K)) ?_ (fun _ => d) ?_ 0
  · intro b hb i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    apply PD.ι_inj
    simpa using hb
  · simp [hd]

theorem map_Dcris_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (c i) (ιV PD (LL := LL) (V := V) (d i))) :
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    have := CrisDR.mul_ι_mem PD ρ (1 : K) hd
    rwa [mulVdR_one] at this
  · intro y hy
    obtain ⟨m, c, d, hd, rfl⟩ := h y hy
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c₀, hc₀⟩ := hb (c i)
    rw [← hc₀, ← ιV_mulVB]
    exact Submodule.mem_map_of_mem (mulVB_mem PD ρ c₀ (hd i))

theorem FildR_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FilCris PD ρ a ⊓ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
      (ιV PD (LL := LL) (V := V)) := by
  apply le_antisymm
  · rintro y ⟨⟨hy, hτ⟩, hF⟩
    rw [← h] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    refine Submodule.mem_map_of_mem ⟨⟨hd, hF⟩, hd, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    apply ιV_injective PD (LL := LL)
    rw [ιV_mulVB, hτ, map_smul]
    rfl
  · rintro _ ⟨d, ⟨⟨hd, hF⟩, -, hτ⟩, rfl⟩
    refine ⟨⟨h ▸ Submodule.mem_map_of_mem hd, ?_⟩, hF⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    obtain ⟨c₀, rfl⟩ := hb c
    rw [← ιV_mulVB, hτ, map_smul]
    rfl

end Abstract

theorem map_Dcris_eq_DdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → (Dcris (P.PD K) ρ).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) = DdR (P.PD K) ρ ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V ∧ ∀ a : ℤ, FildR (P.PD K) ρ τ a = (FilCris (P.PD K) ρ a ⊓ DcrisL (P.PD K) ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) := by
  intro l _ P AI T K LL hb V _ _ _ _ _ ρ hc
  obtain ⟨hdr, hspan⟩ := CrisDR.isDR_of_isCrys l P AI T K LL V ρ hc
  have h := map_Dcris_eq (P.PD K) ρ hb.2 hspan
  refine ⟨h, fun τ => ?_⟩
  obtain ⟨h1, -, h2⟩ := (_root_.GlobalTheory.Per.Components.components_finrank l P AI T K LL V ρ).1 τ
  exact ⟨h1, h2 hdr, FildR_eq (P.PD K) ρ hb.2 h τ⟩

end GlobalTheory.Per.DdREqDcris
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemHeckeEigOfImageMovedByCentre
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PendOf.CenEig

theorem onMt_mem_typeSum (D : D7) (i : D.nd.Loc) (hC : OnMtPreservesTypeV D) (c : MonoidAlgebra ℂ (G0g D.nd))
    (o : Option (D.nd.X i)) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (hF : F ∈ typeSum D i o) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c F ∈ typeSum D i o := by
  have h : typeSum D i o ≤ (typeSum D i o).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c) := by
    refine iSup₂_le fun P hP G hG => ?_
    exact (le_biSup (D.naut.typeV i) hP : D.naut.typeV i P ≤ typeSum D i o) (hC i P c G hG)
  exact h hF

theorem mem_heckeEig_of_mem_typeSum (D : D7) (i : D.nd.Loc) (S : Sec D i) (x : D.nd.X i)
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) (hw : S.Φ w ∈ typeSum D i (some x)) :
    w ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  classical
  have hvtop : w ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ w).1 hvtop
  have hΦv : S.Φ w = ∑ y ∈ f.support, S.Φ (f y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, Finsupp.sum, map_sum]
  have hind := GlobalTheory.PendOf.PrTypeProof.typeSum_indep D i
  have key : ∀ y, y ≠ x → f y = 0 := by
    intro y hy
    by_cases hs : y ∈ f.support
    · have e : S.Φ (f y) = S.Φ w - ∑ y' ∈ f.support.erase y, S.Φ (f y') := by
        rw [hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : S.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o := by
        rw [e]
        refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun y' hy' => ?_)
        · exact Submodule.mem_iSup_of_mem (some x)
            (Submodule.mem_iSup_of_mem (fun e' => hy (Option.some_injective _ e').symm) hw)
        · refine Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (S.eig y' _ (hf y')))
          exact fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')
      have h0 : S.Φ (f y) = 0 := (Submodule.disjoint_def.1 (hind (some y))) _ (S.eig y _ (hf y)) m2
      exact S.inj (h0.trans (map_zero S.Φ).symm)
    · exact Finsupp.notMem_support_iff.1 hs
  rw [← hsum, Finsupp.sum]
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hyp : y = x
  · subst hyp; exact hf y
  · rw [key y hyp]
    exact Submodule.zero_mem _

theorem main : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D → ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x : D.nd.X i) (u w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)), u ∈ heckeEig (D.nd.T i) (D.nd.act i) x → S.Φ w = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ u) → w ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  intro D i S hC c x u w hu hw
  refine mem_heckeEig_of_mem_typeSum D i S x w ?_
  rw [hw]
  exact onMt_mem_typeSum D i hC c _ _ (S.eig x u hu)

end GlobalTheory.PendOf.CenEig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.ScalarInvariants

theorem eq_zero_of_scalar {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (d : O) (hd : d ≠ 1)
    (x : Fin n → FractionRing O)
    (h : ((d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O))).mulVec x = x) : x = 0 := by
  have e : (d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O)) =
      algebraMap O (FractionRing O) d • (1 : Matrix (Fin n) (Fin n) (FractionRing O)) := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have h1 : algebraMap O (FractionRing O) d - 1 ≠ 0 := fun h0 =>
    hd (IsFractionRing.injective O (FractionRing O) (by rw [map_one]; exact sub_eq_zero.1 h0))
  have h2 : (algebraMap O (FractionRing O) d - 1) • x = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left h1

theorem inv_unit_smul_one {O : Type} [CommRing O] {n : ℕ} (d : Oˣ) :
    ((d : O) • (1 : Matrix (Fin n) (Fin n) O))⁻¹ = ((d⁻¹ : Oˣ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.inv_mul, one_smul]

theorem noInv_pD : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → ∀ v ∈ D.ntw.pD i,
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h v hv
  have hlp : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hv
  have hp : (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ z ∈ Dec (F := D.host.E) A,
      ∃ d : (D.ntw.O0 i)ˣ, d ≠ 1 ∧
        Tmat i s z = (d : D.ntw.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) ∧ eps0 D.ntw i z = 1 := by
    intro A hA
    have h15 := D.ntw.delta_15 i v hv A hA
    obtain ⟨z, hzA, hz⟩ : ∃ z ∈ Ine (F := D.host.E) A, D.ntw.delta i z ≠ 1 := by
      by_contra hc
      push Not at hc
      have hb : (Ine (F := D.host.E) A).map (D.ntw.delta i) = ⊥ :=
        (Subgroup.map_eq_bot_iff _).2 fun z hz => hc z hz
      rw [hb, Subgroup.card_bot] at h15
      exact absurd h15 (by norm_num)
    have h1 : D.ntw.rhoS i s z = 1 := h v hl hg A hA z hzA
    have h2 : chiS i s z = if D.ntw.side i s then D.ntw.delta i z else (D.ntw.delta i z)⁻¹ :=
      D.ntw.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
    refine ⟨z, Ine_le_Dec A hzA, (chiS i s z)⁻¹, ?_, ?_, ?_⟩
    · rw [h2]
      split_ifs
      · exact inv_ne_one.2 hz
      · rw [inv_inv]; exact hz
    · rw [Tmat, h1, Units.val_one]
    · have h4 : cycZ D.host.E D.nd.Om (D.ntw.l i) z = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
        rw [ReciprocityTheory.Gal.cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
        simp
      simp [eps0, h4]
  refine ⟨fun A hA x hx => ?_, fun A hA x hx => ?_⟩
  · obtain ⟨z, hz, d, hd, hT, -⟩ := key A hA
    have e := hx z hz
    rw [hT] at e
    exact eq_zero_of_scalar _ (fun h0 => hd (Units.ext h0)) x e
  · obtain ⟨z, hz, d, hd, hT, he⟩ := key A hA
    have e := hx z hz
    rw [Tdual, hT, he, inv_unit_smul_one, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one] at e
    exact eq_zero_of_scalar _ (fun h0 => inv_ne_one.2 hd (Units.ext h0)) x e

end GlobalTheory.TripleGal.ScalarInvariants
end

