module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0147
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowModelOfPointModels
section
noncomputable section

namespace GlobalTheory.RowModelRoad

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.BlockComplement GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

section Twist

variable {Γ O : Type} [Group Γ] [CommRing O] {n : ℕ}

end Twist

section Lift

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

end Lift

section Eig

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) (i : N.Loc)

theorem frobEig_block (θ : A.CG 1) (t : ℕ) (w : PlE H) (b : ℂ) (hu : A.unr (A.locG θ w))
    (hb : A.frobEig (A.locG θ w) = {b}) :
    A.unr (spehLoc N A ⟨1, θ, t⟩ w) ∧ A.frobEig (spehLoc N A ⟨1, θ, t⟩ w) =
      ((List.range t : List ℕ) : Multiset ℕ).map
        fun k : ℕ => b * ((normV w : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 - k : ℝ)) : ℂ) := by
  unfold spehLoc
  dsimp only
  induction List.range t with
  | nil => exact ⟨A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    have h1 := (A.unr_tw _ (((t : ℝ) - 1) / 2 - k)).2 hu
    refine ⟨(A.unr_sum _ _).2 ⟨h1, ih.1⟩, ?_⟩
    refine (A.frobEig_sum _ _ h1 ih.1).trans ?_
    rw [ih.2, A.frobEig_tw _ _ hu, hb]
    simp

end Eig

variable {D : D7}

end GlobalTheory.RowModelRoad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SPiTopEqSTLoc
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.ConjLatticeSelmer

theorem extCond_eq_bkG (L : LocTheory) {l₁ l₂ : ℕ} [i₁ : Fact l₁.Prime] [i₂ : Fact l₂.Prime] (h : l₁ = l₂)
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [Algebra ℤ_[l₁] O₀] [Module.Finite ℤ_[l₁] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l₂] O] [Module.Finite ℤ_[l₂] O] [TopologicalSpace O]
    (B₀ : LocBridge l₁ E Ω Gw O₀) (B : LocBridge l₂ E Ω Gw O) (h₀ : ∀ x, x ∈ A ↔ ‖B₀.j x‖ ≤ 1)
    (h₁ : ∀ x, x ∈ A ↔ ‖B.j x‖ ≤ 1) (f : O₀ →+* O) (hf : Function.Injective f) {k : ℕ}
    (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (M : ↥Gw →* Matrix (Fin k) (Fin k) O) (hM : M = mapM f M₀) :
    extCond f hf (WKG M₀) (Br.bkG B₀ (L l₁) (WKG M₀) M₀) (WKG M) = Br.bkG B (L l₂) (WKG M) M := by
  subst h hM
  cases Subsingleton.elim i₁ i₂
  obtain ⟨σ, hσ⟩ := GlobalTheory.EmbUnitBallConj.exists_conj l₁ Ω B₀.j B.j fun x => (h₀ x).symm.trans (h₁ x)
  have he : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l₁) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l₁) * σ⁻¹ := by
    intro g
    refine GlobalTheory.padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed l₁ Ω B.j _ _ fun x => ?_
    rw [B.e_comm, ← hσ, ← hσ, ← B₀.e_comm]
    simp
  have hz := DFunLike.congr_fun
    (padicInt_hom_ext (natCast_mem_maximalIdeal O) (f.comp (algebraMap ℤ_[l₁] O₀)) (algebraMap ℤ_[l₁] O))
  exact le_antisymm (GlobalTheory.BlochKatoBaseChangeLe.extCond_le_bkG l₁ (L l₁) E Ω Gw O₀ O B₀ B σ he f hf hz k M₀)
    (GlobalTheory.BlochKatoBaseChange.bkG_le_extCond l₁ (L l₁) E Ω Gw O₀ O B₀ B σ he f hf hz k M₀)

variable (D : D7)

theorem selT_eq_selG (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.nd.O a)ˣ)
    (hψ : ∀ v ∈ placesOver D.host.E (D.nd.l a), ∀ g ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ g = 1) :
    selT D.loc D.ntwbr _ s (D.nd.Q a) (D.ntw.twist₂ a) (twO_inj D.ntw a) ψ =
      Br.selG D.nd.plOm (D.nd.l a) (D.loc (D.nd.l a)) (D.nbr a) (↑(D.nd.S a) ∪ ↑(D.nd.Q a))
        (latTpsi D.ntw _ s (D.ntw.twist₂ a) ψ) := by
  have hl := D.ntw.twOf_l a
  have hS : setS D.ntw (D.ntw.twOf a) = ↑(D.nd.S a) := by
    rw [← TwistedTriples.badS_eq D a]
    unfold setS TwistedTriples.badS
    rw [hl]
  unfold selT Br.selG
  congr 1
  funext v
  unfold Formalism.GaloisCohomology.bkCond
  rw [hS]
  by_cases hv : v ∈ placesOver D.host.E (D.nd.l a)
  · have hv' : v ∈ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)) := by rw [hl]; exact hv
    refine (if_pos hv').trans (Eq.trans ?_ (if_pos hv).symm)
    unfold condL Br.LlG
    rw [dite_eq_left hv, dite_eq_left hv']
    have := IsAlgClosure.isAlgClosed D.host.E (K := D.nd.Om)
    refine extCond_eq_bkG D.loc hl (D.nd.plOm.1 v) (D.ntwbr _ v hv') (D.nbr a v hv) (D.ntwbr_ind _ v hv')
      (D.nbr_ind a v hv) (D.ntw.twist₂ a) (twO_inj D.ntw a) ((latT D.ntw _ s).comp (decS D.nd v))
      ((latTpsi D.ntw _ s (D.ntw.twist₂ a) ψ).comp (decS D.nd v)) ?_
    ext g i j
    simp [latTpsi, twistM, mapM, hψ v hv g.1 g.2]
  · have hv' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)) := by rw [hl]; exact hv
    exact (if_neg hv').trans (if_neg hv).symm

theorem nlen_congr {O : Type} [CommRing O] (l : ℕ) (M N : Type) [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (h : Module.length O M = Module.length O N) :
    nlen (O := O) l M = nlen (O := O) l N := by
  unfold nlen lenUnit
  rw [h]

theorem sPiTop_eq_sTLoc (a : D.nd.Loc) (π : D.nd.X a)
    (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (s : D.ntw.Sig (D.ntw.twOf a))
    (U : GL (Fin D.R.r) (D.nd.O a))
    (hU : ∀ g, WpO D.nd a ρ π g * (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) =
      (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) * latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g) :
    sPiTop D a ρ π = sTLoc D a s := by
  unfold sPiTop sTLoc sT
  rw [selT_eq_selG D a s _ fun v hv => D.ntw.psiL_l a v hv _ (D.nd.plOm.2 v), D.ntw.twOf_l]
  exact nlen_congr _ _ _ (GlobalTheory.T.selG_length_eq_of_conj _ _ D.nd.plOm (D.nd.l a) (D.nd.O a) (D.loc (D.nd.l a)) (D.nbr a)
    (↑(D.nd.S a) ∪ ↑(D.nd.Q a)) _ _ _ U hU).symm

end GlobalTheory.ConjLatticeSelmer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateDualFil

section Linear

variable {G : Type} [Group G] {LL : Type} [Field LL] (L : Type) [Field L] [Algebra LL L]
  {V : Type} [AddCommGroup V] [Module LL V] {V' : Type} [AddCommGroup V'] [Module LL V']

def extRep (ρ : Representation LL G V) : Representation L G (L ⊗[LL] V) where
  toFun g := (ρ g).baseChange L
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem extRep_tmul (ρ : Representation LL G V) (g : G) (a : L) (x : V) :
    extRep L ρ g (a ⊗ₜ[LL] x) = a ⊗ₜ[LL] ρ g x := rfl

theorem exists_ext_pairing [FiniteDimensional LL V] (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (hm : Function.Bijective m.flip) :
    ∃ m' : L ⊗[LL] V →ₗ[L] L ⊗[LL] V' →ₗ[L] L, Function.Bijective m' ∧
      ∀ (a b : L) x y, m' (a ⊗ₜ[LL] x) (b ⊗ₜ[LL] y) = a * b * algebraMap LL L (m x y) := by
  obtain ⟨v, w, hvw⟩ := GlobalTheory.DRFil.exists_dual_bases m hm
  let v' := Algebra.TensorProduct.basis L v
  let w' := Algebra.TensorProduct.basis L w
  let e := v'.equiv w'.dualBasis (Equiv.refl _)
  refine ⟨e.toLinearMap, e.bijective, fun a b x y => ?_⟩
  have h1 : ∀ i, e.toLinearMap (a ⊗ₜ[LL] v i) (b ⊗ₜ[LL] y) = a * b * algebraMap LL L (m (v i) y) := by
    intro i
    have h2 : a ⊗ₜ[LL] v i = a • v' i := by
      simp [v', Algebra.TensorProduct.basis_apply, smul_tmul']
    have h3 : m (v i) y = w.repr y i := by
      conv_lhs => rw [← w.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hvw, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [h2, map_smul, h3]
    simp only [e, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, LinearMap.smul_apply,
      Basis.dualBasis_apply, w', Algebra.TensorProduct.basis_repr_tmul]
    simp [mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← v.sum_repr x, tmul_sum, map_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h4 : a ⊗ₜ[LL] (v.repr x i • v i) = algebraMap LL L (v.repr x i) • (a ⊗ₜ[LL] v i) := by
    rw [algebraMap_smul, tmul_smul]
  rw [h4, map_smul, LinearMap.smul_apply, h1, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    map_mul]
  ring

end Linear

theorem exists_eq_bot {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hle : ∀ a, F a ≤ D) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0) : ∃ b : ℤ, ∀ a, b ≤ a → F a = ⊥ := by
  have hfin : ∀ a, FiniteDimensional k (F a) := fun a => Submodule.finiteDimensional_of_le (hle a)
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ∀ a, finrank k (F b) ≤ finrank k (F a) :=
    ⟨Function.argmin fun a => finrank k (F a), fun a => Function.argmin_le (fun a => finrank k (F a)) a⟩
  have h1 : ∀ a, b ≤ a → F a = F b := fun a ha => Submodule.eq_of_le_of_finrank_le (hF ha) (hb a)
  refine ⟨b, fun a ha => ?_⟩
  rw [h1 a ha, eq_bot_iff]
  intro x hx
  refine hsep x fun c => ?_
  rcases le_total b c with h | h
  · rw [h1 c h]; exact hx
  · exact hF h hx

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_fil_zero_add (ρ : Representation LL G V) (ρ' : Representation LL G V')
    [FiniteDimensional LL ↥(DdR PD ρ)] [FiniteDimensional LL ↥(DdR PD ρ')] (τ : K →ₐ[Qp] LL)
    (h : ∀ a, multV PD ρ' τ (-a - 1) = multV PD ρ τ a) :
    finrank LL ↥(FildR PD ρ' τ 0) + finrank LL ↥(FildR PD ρ τ 0) = finrank LL ↥(DdRE PD ρ τ) := by
  have : FiniteDimensional LL ↥(DdRE PD ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  obtain ⟨b, hb⟩ := GlobalTheory.Per.FilCount.exists_eq_of_exhaustive (DdRE PD ρ τ) (FildR PD ρ τ)
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.DRFil.FilV_antitone PD hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.DRFil.exists_mem_FilV PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)
  obtain ⟨c, hc⟩ := exists_eq_bot (DdR PD ρ') (FildR PD ρ' τ)
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.DRFil.FilV_antitone PD hab))
    (fun a => le_trans inf_le_left inf_le_left)
    (fun x hx => GlobalTheory.DRFil.eq_zero_of_forall_mem_FilV PD (LL := LL) x fun a => (hx a).2)
  let s : ℤ → ℕ := fun a => finrank LL ↥(FildR PD ρ' τ (-a)) + finrank LL ↥(FildR PD ρ τ a)
  have hs : ∀ a, s (a + 1) = s a := fun a => by
    have h1 := h a
    unfold multV at h1
    rw [show -a - 1 + 1 = -a by ring, show -a - 1 = -(a + 1) by ring] at h1
    simp only [s]
    omega
  have hs0 : ∀ a, s a = s 0 := fun a => by
    induction a using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hs, ih]
    | pred n ih => rw [← hs, sub_add_cancel, ih]
  have h2 := hs0 (min b (-c))
  simp only [s] at h2
  rw [hb _ (min_le_left _ _), hc _ (by omega), finrank_bot, zero_add, neg_zero] at h2
  exact h2.symm

theorem descend (L : Type) [Field L] [Algebra Qp L] [Algebra LL L] [IsScalarTower Qp LL L]
    [FiniteDimensional LL L] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (H : ∀ (W : Type) [AddCommGroup W] [Module L W] [Module Qp W] [IsScalarTower Qp L W]
      [FiniteDimensional L W] (σ : Representation L G W)
      (W' : Type) [AddCommGroup W'] [Module L W'] [Module Qp W'] [IsScalarTower Qp L W']
      [FiniteDimensional L W'] (σ' : Representation L G W') (n : W →ₗ[L] W' →ₗ[L] L),
      Function.Bijective n → (∀ g x y, n (σ g x) (σ' g y) = ((cycLL PD L g : Lˣ) : L) * n x y) →
      IsDR PD σ → IsDR PD σ' ∧
        finrank L ↥(DdR PD σ' ⊓ FilV PD (LL := L) (V := W') 0) +
          finrank L ↥(DdR PD σ ⊓ FilV PD (LL := L) (V := W) 0) = finrank L ↥(DdR PD σ))
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : IsDR PD ρ) (hm : IsDual1 PD ρ ρ' m) :
    IsDR PD ρ' ∧
      finrank LL ↥(DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') 0) +
        finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) = finrank LL ↥(DdR PD ρ) := by
  have hbij : Function.Bijective m.flip := by
    have hi : Function.Injective m.flip := (injective_iff_map_eq_zero _).2 fun y hy =>
      hm.2.2.1 y fun x => LinearMap.congr_fun hy x
    refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi⟩
    rw [← hm.2.2.2]
    exact Subspace.dual_finrank_eq.symm
  obtain ⟨m', hm', hm''⟩ := exists_ext_pairing L m hbij
  obtain ⟨a1, -, -, ⟨a2, -⟩, a3, -⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange PD LL L V (L ⊗[LL] V) ρ (extRep L ρ)
    (TensorProduct.mk LL L V 1) (TensorProduct.isBaseChange LL V L) (fun g x => rfl)
  obtain ⟨b1, -, -, ⟨b2, -⟩, b3, -⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange PD LL L V' (L ⊗[LL] V') ρ' (extRep L ρ')
    (TensorProduct.mk LL L V' 1) (TensorProduct.isBaseChange LL V' L) (fun g x => rfl)
  have hχ : ∀ g, ((cycLL PD L g : Lˣ) : L) = algebraMap LL L ((cycLL PD LL g : LLˣ) : LL) := fun g =>
    IsScalarTower.algebraMap_apply Qp LL L _
  have hinv : ∀ g x y, m' (extRep L ρ g x) (extRep L ρ' g y) = ((cycLL PD L g : Lˣ) : L) * m' x y := by
    intro g x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx', mul_add]
    | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add (f := _), hy, hy', mul_add]
      | tmul b y =>
        rw [extRep_tmul, extRep_tmul, hm'', hm'', hm.1, map_mul, hχ]
        ring
  have hL : IsDR PD (extRep L ρ) := by
    rw [IsDR, a1, a2]; exact h
  obtain ⟨c1, c2⟩ := H _ (extRep L ρ) _ (extRep L ρ') m' hm' hinv hL
  refine ⟨by rw [IsDR, ← b1, ← b2]; exact c1, ?_⟩
  rw [← a2, ← a3, ← b3, c2]

end Period

theorem tateDual_split (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K L : FinExt l) (hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥L.1) = finrank ℚ_[l] ↥K.1)
    (W : Type) [AddCommGroup W] [Module ↥L.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥L.1 W]
    [FiniteDimensional ↥L.1 W] (σ : Representation ↥L.1 ↥(GK K) W)
    (W' : Type) [AddCommGroup W'] [Module ↥L.1 W'] [Module ℚ_[l] W'] [IsScalarTower ℚ_[l] ↥L.1 W']
    [FiniteDimensional ↥L.1 W'] (σ' : Representation ↥L.1 ↥(GK K) W') (n : W →ₗ[↥L.1] W' →ₗ[↥L.1] ↥L.1)
    (hn : Function.Bijective n)
    (hinv : ∀ g x y, n (σ g x) (σ' g y) = ((cycLL (P.PD K) ↥L.1 g : (↥L.1)ˣ) : ↥L.1) * n x y)
    (h : IsDR (P.PD K) σ) :
    IsDR (P.PD K) σ' ∧
      finrank ↥L.1 ↥(DdR (P.PD K) σ' ⊓ FilV (P.PD K) (LL := ↥L.1) (V := W') 0) +
        finrank ↥L.1 ↥(DdR (P.PD K) σ ⊓ FilV (P.PD K) (LL := ↥L.1) (V := W) 0) =
          finrank ↥L.1 ↥(DdR (P.PD K) σ) := by
  have := K.2
  obtain ⟨c1, c2⟩ := GlobalTheory.DRDual.twisted_dual_deRham l P AI T K L W σ W' σ' n 1 hn
    (fun g x y => by rw [zpow_one]; exact hinv g x y) h
  refine ⟨c1, ?_⟩
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K L W σ).1
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K L W' σ').1
  have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥L.1) = finrank ℚ_[l] ↥K.1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
  obtain ⟨d1, d2⟩ := GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc σ
  obtain ⟨-, d3⟩ := GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc σ'
  rw [d1, d2, d3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun τ _ =>
    finrank_fil_zero_add (P.PD K) σ σ' τ fun a => c2 τ a hcard

theorem tateDual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL ↥(GK K) V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : IsDR (P.PD K) ρ) (hm : IsDual1 (P.PD K) ρ ρ' m) :
    IsDR (P.PD K) ρ' ∧
      finrank LL ↥(DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := LL) (V := V') 0) +
        finrank LL ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) 0) =
          finrank LL ↥(DdR (P.PD K) ρ) := by
  obtain ⟨L, ⟨f⟩, hcard, -⟩ := GlobalTheory.exists_finExt_embedding_splitting l K LL
  have := L.2
  letI : Algebra LL ↥L.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL ↥L.1 := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional LL ↥L.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] LL ↥L.1
  exact descend (P.PD K) ↥L.1 (tateDual_split l P AI T K L hcard) ρ ρ' m h hm

theorem main : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm8 D := by
  intro D l _ K
  refine ⟨fun LL _ _ _ O _ _ hO A A' m h hm => ?_, fun LL _ _ _ O _ _ hO A A' m h hm => ?_⟩
  · haveI := hO.2.1
    exact (tateDual l (D.loc l) (D.locA l) (D.locT l) K LL A.ρ A'.ρ m h hm).1
  · haveI := hO.2.1
    exact (tateDual l (D.loc l) (D.locA l) (D.locT l) K LL A.ρ A'.ρ m h hm).2

end GlobalTheory.TateDualFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorBcrisFrobeniusValueEqSumCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.XiDecomp

theorem toBcris_xiExt_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (w : Vec K a ι) (hwS : ∀ τ j, w τ j ∈ invL l (S O K e)) (hw : P.xiExt w ∈ P.MMl) (hd : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl), toBcris t ϖ P ⟨P.xiExt w, hw⟩ = ∑ j, ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) • toBcris t ϖ P ⟨P.xi (fun _ => Pi.single j 1), hd j⟩ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P w hwS hw hd
  have hsum : (⟨P.xiExt w, hw⟩ : P.MMl) = ∑ j, (⟨(fun τ => w τ j) • P.xi (fun _ => Pi.single j 1),
      P.smul_tot_mem_ext (fun τ => hwS τ j) (hd j)⟩ : P.MMl) := by
    apply Subtype.ext
    show P.xiExt w = _
    rw [Submodule.coe_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [eq_sum_bas w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show _ = (fun τ => w τ j) • P.xi (fun _ => Pi.single j 1)
    rw [PhiMod.xiExt_smul_tot, PhiMod.xi_apply, cst_single]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext1 k
  rw [Pi.smul_apply, toBcris_apply, toBcris_apply, smul_eq_mul, ← map_mul]
  congr 1
  funext τ
  apply Subtype.ext
  simp [coordL, Matrix.mulVec_smul]

end GlobalTheory.XiDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorBcrisValueFrobeniusOfInverseEisensteinTwis
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.PhiVal

theorem isCrisVal_phi : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (hφ : D.phi y ∈ D.MMl), IsCrisVal t ϖ D.toPhiMod jB (phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩)) (jB (toBcris t ϖ D.toPhiMod ⟨D.phi y, hφ⟩)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T jB y hY hy hφ
  have hEM : ∀ τ i, E K l e ^ η * y τ i ∈ A O K := fun τ i => mem_tot.1 ((Descent.mem_invOf _).1 hY).1 τ i
  let g : ι → ZMod a → A O K := fun i τ => ⟨E K l e ^ η * y τ i, hEM τ i⟩
  let m : OA l O := frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ η
  refine ⟨m, fun i => frobOA l O (ϖ.iTot t K (g i)), ?_, ?_, ?_⟩
  · rw [map_pow]
    exact (FrobEis.isUnit_toB_frob_eis l a e O ϖ).pow η
  · let EW : ZMod a → invE l e (A O K) := fun _ => ⟨(EIn l e (A O K) : K⟦X⟧), le_away _ _ (EIn l e (A O K)).2⟩
    have h2 : ϖ.iW t K EW = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) :=
      (ϖ.iW_of_mem t K (fun _ => EIn l e (A O K))).trans (congrArg _ (ϖ.iTot_E t K))
    have hA : ∀ i, inclO l O m * frobOW l O (toW t ϖ D.toPhiMod ⟨y, hy⟩ i) =
        inclO l O (frobOA l O (ϖ.iTot t K (g i))) := by
      intro i
      have h1 : ϖ.iW t K (fun τ => ⟨(g i τ : K⟦X⟧), le_away _ _ (g i τ).2⟩) =
          ϖ.iW t K EW ^ η * ϖ.iW t K (fun τ => ⟨y τ i, mem_tot.1 hy τ i⟩) := by
        rw [← map_pow, ← map_mul]
        congr 1
      rw [← frobOW_inclO, ← ϖ.iW_of_mem t K, h1, map_mul, h2, toW_apply, map_pow (inclO l O), map_pow (frobOW l O),
        frobOW_inclO]
    rw [phiW_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, hA i]
  · rw [← LinearEquiv.map_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, toBcris_apply]
    let liftA : (ZMod a → A O K) → ZMod a → invL l (S O K e) :=
      fun F τ => ⟨F τ, le_away _ _ (A_le_S l e (F τ).2)⟩
    have key : liftA (frobAc l fun _ => EIn l e (A O K)) ^ η * coordL D.toPhiMod (invL l (S O K e)) ⟨D.phi y, hφ⟩ i =
        liftA (frobAc l (g i)) := by
      funext τ
      apply Subtype.ext
      have h1 : (coordL D.toPhiMod (invL l (S O K e)) ⟨D.phi y, hφ⟩ i τ : K⟦X⟧) = frob K l (y (τ - 1) i) := by
        change (D.mxInv τ *ᵥ D.phi y τ) i = _
        rw [PhiMod.phi_apply, Matrix.mulVec_mulVec, PhiMod.mxInv_mul_mx, Matrix.one_mulVec, frobV_apply]
      simp only [liftA, Pi.mul_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, h1, coe_frobAc,
        frobTot_apply, g, map_mul, map_pow]
      rw [coe_EIn]
    have h3 := congrArg (ϖ.iB t K) key
    simp only [map_mul, map_pow, liftA, FrobCoord.iB_of_A, ϖ.iTot_frob t K, ϖ.iTot_E t K] at h3
    rw [← h3, map_pow]

end GlobalTheory.BKGal.PhiVal
end
end

