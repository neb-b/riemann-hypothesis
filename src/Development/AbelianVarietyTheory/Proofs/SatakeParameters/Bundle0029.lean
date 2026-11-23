module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0025
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.DataRows

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LaurentConstantTermEqEvalOriginChart
section
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.ResEv

open MvPolynomial

theorem ker_aeval_zero (k : Type) [Field k] (d : ℕ) :
    RingHom.ker (aeval (R := k) (fun _ : Fin d ↦ (0 : k))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p = AddMonoidAlgebra.coeff p 0 := by
      rw [show (fun _ : Fin d ↦ (0 : k)) = 0 from rfl, MvPolynomial.aeval_zero]
      simp [MvPolynomial.constantCoeff_eq]
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp

theorem res_aeval (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F)
    (hx : IsPd k x) (ρ : F →ₗ[k] k) (hρ : IsRes k x ρ) (p : MvPolynomial (Fin d) k) :
    ρ (aeval (fun j : Fin d ↦ x j.succ / x 0) p) = aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_eq_mul]
    by_cases hn : n = 0
    · subst hn
      simp [hρ.1]
    · obtain ⟨j0, hj0⟩ : ∃ j, n j ≠ 0 := by
        by_contra h; push_neg at h; exact hn (Finsupp.ext h)
      have h0 : ∏ j : Fin d, (0 : k) ^ n j = 0 := Finset.prod_eq_zero (Finset.mem_univ j0) (zero_pow hj0)
      rw [h0, smul_zero]
      let m : Fin (d + 1) → ℤ := Fin.cons (-(∑ j, (n j : ℤ))) (fun j ↦ (n j : ℤ))
      have hsum : ∑ i, m i = 0 := by
        rw [Fin.sum_univ_succ]; simp [m]
      have hm : m ≠ 0 := by
        intro h
        have := congrFun h j0.succ
        simp [m] at this
        exact hj0 this
      have hprod : ∏ j : Fin d, (x j.succ / x 0) ^ n j = ∏ i, x i ^ m i := by
        rw [Fin.prod_univ_succ]
        simp only [m, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg]
        rw [Finset.prod_congr rfl (fun j _ ↦ div_pow (x j.succ) (x 0) (n j)), Finset.prod_div_distrib,
          Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast, div_eq_inv_mul]
      rw [hprod, hρ.2 m hsum hm, mul_zero]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]

end GlobalTheory.PD.ResEv

open MvPolynomial in
theorem GlobalTheory.PD.ResEv.chart0 : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∃ ev : rA k x {0} →ₐ[k] k, (∀ a : rA k x {0}, ρ a = ev a) ∧ RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) := by
  intro k _ F _ _ d x hx ρ hρ
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hx 0
  have hv : ∀ p : MvPolynomial (Fin d) k, ((e p : rA k x {0}) : F) = aeval (fun j : Fin d ↦ x j.succ / x 0) p := by
    intro p
    have h1 : ((rA k x {0}).val.comp e.toAlgHom) = aeval (fun j : Fin d ↦ x j.succ / x 0) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [he]
    exact congrArg (fun f => f p) (congrArg DFunLike.coe h1)
  refine ⟨(aeval (R := k) (fun _ : Fin d ↦ (0 : k))).comp e.symm.toAlgHom, fun a => ?_, ?_⟩
  · have := GlobalTheory.PD.ResEv.res_aeval k F d x hx ρ hρ (e.symm a)
    rw [← hv, AlgEquiv.apply_symm_apply] at this
    simpa using this
  · have ht : (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) = (e.toRingEquiv : MvPolynomial (Fin d) k →+* rA k x {0}) '' Set.range X := by
      rw [← Set.range_comp]
      congr 1
      funext j
      apply Subtype.ext
      simp [he]
    rw [ht, ← Ideal.map_span, ← GlobalTheory.PD.ResEv.ker_aeval_zero]
    ext a
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
section
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

variable {k : Type} [CommRing k] {X : Scheme.{0}}

theorem formPull_id (s : X ⟶ Sp k) (j : ℕ) (U : X.Opens) (x : OmU s U j) :
    formPull (f := 𝟙 X) (Category.id_comp s) U j x = x :=
  SemiHom.mOm_id _ (fun _ ↦ rfl) x

theorem omegaPull_id (s : X ⟶ Sp k) (j : ℕ) :
    omegaPull (f := 𝟙 X) (Category.id_comp s) j =
      (Scheme.Modules.pushforwardId X).inv.app (Omega s j) := by
  refine (Equiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  ext U x
  exact congrArg ((toOmega s j).app U).hom (formPull_id s j U.unop x)

theorem hodgePull_id (s : X ⟶ Sp k) (j q : ℕ) (x : hodgeH s j q) :
    hodgePull (f := 𝟙 X) (Category.id_comp s) j q x = x := by
  letI := algΓ s
  apply (cohOn.toH' (Omega s j) ⊤ q).injective
  refine (cohOn.toH'_pull (appTop_algebraMap (Category.id_comp s))
    (omegaPull (Category.id_comp s) j) (le_refl ((𝟙 X) ⁻¹ᵁ ⊤)) (n := q) x).trans ?_
  rw [omegaPull_id]
  exact (SheafPull.pull_id (X := X.toTopCat) (𝟙 ((toAbSheaf X).obj (Omega s j))) q
    (homOfLE (le_refl ⊤)) _).trans (by rw [SheafLES.map_id]; exact SheafLES.res_id _ _ _)

end GlobalTheory.HodgeCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
section
noncomputable section

namespace GlobalTheory.RowSatakeBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.LatHecke

section Local

variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]

def IsUnitarySatake (r : ℕ) (β : Multiset ℂ) : Prop :=
  β.card = r ∧
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
    (ρ : Representation ℂ (GL (Fin r) K) V) (v : V),
    (∀ g x, ‖ρ g x‖ = ‖x‖) ∧ v ≠ 0 ∧
    (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) ∧
    ∀ k ≤ r, ∀ s : Finset (GL (Fin r) K),
      Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) →
      ∑ g ∈ s, ρ g v =
        ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * β.esymm k) • v

variable {O K}

theorem IsUnitarySatake.norm_le {r : ℕ} {β : Multiset ℂ} (h : IsUnitarySatake O K r β) :
    ∀ b ∈ β, ‖b‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  obtain ⟨hc, V, _, _, ρ, v, hρ, hv, hfix, hT⟩ := h
  exact _root_.GlobalTheory.LatHecke.satake_bound_of_isometric_spherical O K r V ρ v β hc hρ hv hfix hT

end Local

section Completion

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem finite_residue : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) :=
  Formalism.UG.P.tjcosets_finite w

theorem qRes_eq_normV [Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E))] :
    qRes (w.adicCompletionIntegers E) = normV w := by
  unfold qRes normV
  rw [Formalism.UG.P.tjcosets_card_residue, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

def IsUnitarySatakeAt (r : ℕ) (β : Multiset ℂ) : Prop :=
  haveI := finite_residue w
  IsUnitarySatake (w.adicCompletionIntegers E) (w.adicCompletion E) r β

variable {w}

theorem IsUnitarySatakeAt.norm_le {r : ℕ} {β : Multiset ℂ} (h : IsUnitarySatakeAt w r β) :
    ∀ b ∈ β, ‖b‖ ≤ ((normV w : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  have := finite_residue w
  rw [← qRes_eq_normV w]
  exact IsUnitarySatake.norm_le h

end Completion

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def UnitarySphericalComponent : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
    ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
      IsUnitarySatakeAt w R.r ((A.frobEig (A.locW i σ w)).map (·⁻¹)) ∧
      IsUnitarySatakeAt w R.r (A.frobEig (A.locW i σ w))

theorem rowSizeLe_of_component (h : UnitarySphericalComponent N A) :
    GlobalTheory.ThetaExh.RowSizeLe N A :=
  fun i σ hσ w hw hu => (h i σ hσ w hw hu).2.norm_le

theorem rowEigSmall_of_component : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R)
    (N : NData R H what₂) (A : NAut N),
    UnitarySphericalComponent N A → GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.RowEigSmall N A :=
  fun _ _ _ N A h => GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.rowEigSmall_of_le N A (rowSizeLe_of_component N A h)

theorem rowSize_of_component (h : UnitarySphericalComponent N A) : GlobalTheory.ThetaExh.RowSize N A :=
  rowEigSmall_of_component _ _ _ N A h

end GlobalTheory.RowSatakeBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SemisimpleDecomp

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

theorem isInv_inf {ρ : Γ →* GL (Fin a) k} {U V : Submodule k (Fin a → k)} (hU : IsInv ρ U)
    (hV : IsInv ρ V) : IsInv ρ (U ⊓ V) :=
  fun g v hv => ⟨hU g v hv.1, hV g v hv.2⟩

theorem isInv_top (ρ : Γ →* GL (Fin a) k) : IsInv ρ ⊤ := fun _ _ _ => Submodule.mem_top

theorem exists_irr_le {ρ : Γ →* GL (Fin a) k} {U : Submodule k (Fin a → k)} (hU : IsInv ρ U)
    (h0 : U ≠ ⊥) : ∃ W, W ≤ U ∧ IsIrrSub ρ W := by
  obtain ⟨W, ⟨hW0, hWi, hWU⟩, hmin⟩ := (wellFounded_lt (α := Submodule k (Fin a → k))).has_min
    {W | W ≠ ⊥ ∧ IsInv ρ W ∧ W ≤ U} ⟨U, h0, hU, le_rfl⟩
  refine ⟨W, hWU, hW0, hWi, fun W' hle hi => ?_⟩
  by_cases h : W' = ⊥
  · exact Or.inl h
  · right
    by_contra hne
    exact hmin W' ⟨h, hi, hle.trans hWU⟩ (lt_of_le_of_ne hle hne)

theorem disjoint_sup_of_le {α : Type*} [Lattice α] [OrderBot α] [IsModularLattice α] {x b c w : α}
    (hx : x ≤ c) (hb : b ≤ c) (hxb : Disjoint x b) (hw : Disjoint w c) : Disjoint x (w ⊔ b) := by
  have hc : (b ⊔ w) ⊓ c = b := by
    rw [sup_inf_assoc_of_le w hb, hw.eq_bot, sup_bot_eq]
  rw [disjoint_iff_inf_le]
  calc x ⊓ (w ⊔ b) ≤ x ⊓ b := by
        refine le_inf inf_le_left ?_
        exact (le_inf (inf_le_right.trans (sup_comm w b).le) (inf_le_left.trans hx)).trans hc.le
    _ ≤ ⊥ := hxb.le_bot

theorem exists_decomp {ρ : Γ →* GL (Fin a) k} (hρ : IsSSRep ρ) (U : Submodule k (Fin a → k))
    (hU : IsInv ρ U) : ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)),
      iSupIndep Vs ∧ iSup Vs = U ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  induction U using WellFoundedLT.induction with
  | _ U ih =>
  by_cases h0 : U = ⊥
  · exact ⟨0, Fin.elim0, fun i => i.elim0, by simp [h0], fun j => j.elim0⟩
  obtain ⟨W, hWU, hW⟩ := exists_irr_le hU h0
  obtain ⟨W', hW'i, hc⟩ := hρ W hW.2.1
  have hlt : U ⊓ W' < U := by
    refine lt_of_le_of_ne inf_le_left fun heq => hW.1 ?_
    have hle : W ≤ W' := hWU.trans (heq.symm ▸ inf_le_right)
    exact hc.disjoint.eq_bot_of_le hle
  obtain ⟨n, Vs, hind, hsup, hirr⟩ := ih _ hlt (isInv_inf hU hW'i)
  have hVs : ∀ j, Vs j ≤ U ⊓ W' := fun j => hsup ▸ le_iSup Vs j
  refine ⟨n + 1, Fin.cons W Vs, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · refine hc.disjoint.mono_right (iSup₂_le fun j hj => ?_)
      refine Fin.cases (fun h => absurd rfl h) (fun j _ => ?_) j hj
      simpa using (hVs j).trans inf_le_right
    · have hle : (⨆ (j) (_ : j ≠ Fin.succ i), (Fin.cons W Vs : Fin (n + 1) → _) j) ≤
          W ⊔ ⨆ (j) (_ : j ≠ i), Vs j := by
        refine iSup₂_le fun j hj => ?_
        refine Fin.cases (fun _ => ?_) (fun j hj => ?_) j hj
        · simp
        · have hji : j ≠ i := fun h => hj (h ▸ rfl)
          simp only [Fin.cons_succ]
          exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ i) => Vs j) j hji)
      simp only [Fin.cons_succ]
      refine (disjoint_sup_of_le (hVs i) (iSup₂_le fun j _ => hVs j) (hind i)
        (hc.disjoint.mono_right inf_le_right)).mono_right hle
  · have hS : iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) = W ⊔ iSup Vs := by
      refine le_antisymm (iSup_le fun j => ?_) (sup_le ?_ (iSup_le fun j => ?_))
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · simpa using le_sup_of_le_right (le_iSup Vs j)
      · simpa using le_iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) 0
      · simpa using le_iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) j.succ
    rw [hS, hsup, inf_comm, ← sup_inf_assoc_of_le W' hWU, hc.sup_eq_top, top_inf_eq]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hW
    · simpa using hirr j

end GlobalTheory.SemisimpleDecomp

theorem GlobalTheory.semisimple_matrix_rep_decomp : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ}
    (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)),
      DirectSum.IsInternal Vs ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  intro k Γ _ _ a ρ hρ
  obtain ⟨n, Vs, hind, hsup, hirr⟩ :=
    GlobalTheory.SemisimpleDecomp.exists_decomp hρ ⊤ (GlobalTheory.SemisimpleDecomp.isInv_top ρ)
  exact ⟨n, Vs, (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Vs).2 ⟨hind, hsup⟩,
    hirr⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
section
noncomputable section

namespace GlobalTheory.LocalInv

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

abbrev Eig : Type := ∀ w : PlE H, A.LP w → G H.E N.Om → Multiset ℂ

def FrobLift (w : PlE H) (σ : G H.E N.Om) : Prop := IsFrob (F := H.E) (N.plOm.1 w) (normV w) σ

def TemperedSizes (eig : Eig N A) : Prop := ∀ w σ, FrobLift N w σ → ∀ a : A.LP w, A.tempered a →
  ∀ α ∈ eig w a σ, ((normV w : ℕ) : ℝ) ^ (-(((A.lpDim a : ℝ) - 1) / 2)) ≤ ‖α‖ ∧
    ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((A.lpDim a : ℝ) - 1) / 2)

def EtaType : Prop := A.csd A.etaT ∧ ∀ τ, ∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2

def WeightRegular : Prop := ∀ (i : N.Loc) (_ : A.AV i) (τ : H.E →+* ℂ), (A.infWt i τ).Nodup ∧
  ∀ z ∈ A.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((R.nV : ℂ) - 1) / 2

def GoodCuspidal : Prop := ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
  HasParamX N A i x Sig → goodSig N A Sig → IsCuspIso N A Sig

theorem weightRegular_of_ext (B : NBC A) : WeightRegular N A := fun i P τ => by
  rw [B.embAV_inf i P]
  exact B.infW_alg _ _ τ

theorem one_lt_normV (w : PlE H) : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by
  have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 H.E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card (𝓞 H.E ⧸ w.asIdeal))

theorem normV_ne_zero (w : PlE H) : ((normV w : ℕ) : ℂ) ≠ 0 := by
  have h := one_lt_normV w
  have : (normV w : ℕ) ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  exact_mod_cast this

theorem r_odd (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have := R.two_le_m
  exact ⟨a + b - 1, by unfold Ranks.r; omega⟩

theorem r_add_le (R : Ranks) : R.r + 5 ≤ R.t := R.rank_add_five_le

theorem chi_apply (i : N.Loc) (k : ℕ) (hk : k < R.t) (g : G H.E N.Om) :
    N.chi i (k + 1) g = N.chi i 1 g * ((eps N i g) ^ k)⁻¹ := by
  rw [N.chi_def i (k + 1) (by omega) (by omega)]
  simp [eps]

theorem eps_cont (i : N.Loc) : Continuous fun g => ((eps N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((eps N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := r_add_le R
    rw [← Units.val_mul, chi_apply N i 1 (by omega)]
    simp
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

theorem iota_eps (i : N.Loc) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    iotaO N A i ((eps N i σ : (N.O i)ˣ) : N.O i) = ((normV w : ℕ) : ℂ) := by
  have h := cycZ_of_isFrob (l := N.l i) hw hB hσ
  have : ((eps N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [this, h]
  simp

theorem galPol_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) :
    galPol A (A.lpSum a b) = galPol A a * galPol A b := by
  unfold galPol
  rw [A.frobEig_sum a b ha hb, Multiset.map_add (f := _), Multiset.prod_add]

theorem galPol_tw_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) (s : ℝ) :
    galPol A (A.lpTw (A.lpSum a b) s) = galPol A (A.lpTw a s) * galPol A (A.lpTw b s) := by
  rw [A.lpTw_sum, galPol_sum N A _ _ ((A.unr_tw _ _).2 ha) ((A.unr_tw _ _).2 hb)]

theorem galPol_tw_zero (w : PlE H) (s : ℝ) : galPol A (A.lpTw (A.lpZero w) s) = 1 := by
  unfold galPol
  rw [A.frobEig_tw _ _ (A.lpZero_unr w), A.frobEig_zero]
  simp

theorem galPol_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (e : ℝ → ℝ) (s : ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) ∧
    galPol A (A.lpTw (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) s) =
      (L.map fun k => galPol A (A.lpTw a (e k + s))).prod := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, by simpa using galPol_tw_zero N A w s⟩
  | cons k L ih =>
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 ha, ih.1⟩, ?_⟩
    rw [List.foldr_cons, galPol_tw_sum N A _ _ ((A.unr_tw _ _).2 ha) ih.1, ih.2, A.lpTw_add,
      List.map_cons, List.prod_cons]

theorem list_coe {α β : Type} (f : α → β) (L : List α) :
    (do let a ← L; pure (f a) : List β) = L.map f := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa using ih

theorem galPol_speh (p : Part A.CG) (w : PlE H) (ha : A.unr (A.locG p.π w)) (s : ℝ) :
    A.unr (spehLoc N A p w) ∧ galPol A (A.lpTw (spehLoc N A p w) s) =
      ∏ k ∈ Finset.range p.d, galPol A (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + s)) := by
  have h := galPol_foldr N A _ ha (fun k => ((p.d : ℝ) - 1) / 2 - k) s
    (do let a ← List.range p.d; pure ((a : ℕ) : ℝ))
  refine ⟨h.1, h.2.trans ?_⟩
  rw [list_coe, List.map_map, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  rfl

theorem galPol_block (i : N.Loc) {w : PlE H} (hw : SplitOut N i w) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) (u : ℝ) :
    galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + u)) =
      X - C (iotaO N A i ((N.chi i 1 σ : (N.O i)ˣ) : N.O i) * ((normV w : ℕ) : ℂ) ^ ((u : ℝ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := A.chi_mu i w hw
  unfold galPol
  rw [← A.lpTw_add, A.frobEig_tw _ _ ((A.unr_tw _ _).2 h1), h2 B σ hB hσ]
  simp [iotaO]

theorem part_alg (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (P : A.AV i)
    (Pa : List (Part A.CG)) (hB : IsBCV N A i P Pa) (p : Part A.CG) (hp : p ∈ Pa) (ha : Odd p.a)
    (hd : Odd p.d) : A.csd (A.tw p.π A.etaT) ∧ A.ralg (A.tw p.π A.etaT) := by
  refine ⟨A.csd_tw _ _ hη.1 (hB.1 p hp).2.2, (A.ralg_def _).2 fun τ => ?_⟩
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
  obtain ⟨k0, hk0⟩ := hη.2 τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hle : (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ A.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd.pos)
  rw [A.infG_tw _ _ τ s hs]
  refine ⟨(Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle (hW i P τ).1)).map (add_left_injective s), ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  obtain ⟨a, ha⟩ := ha
  obtain ⟨d, hd⟩ := hd
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  refine ⟨k + k0 + r + t + 1 - d - a, ?_⟩
  rw [Ranks.nV, hr, ht, hd] at hk
  rw [hk0, ha]
  push_cast at hk ⊢
  linear_combination hk

end GlobalTheory.LocalInv
end
end

