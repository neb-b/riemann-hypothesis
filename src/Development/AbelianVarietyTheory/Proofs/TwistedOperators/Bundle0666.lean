module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearRightLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.Unf
open GlobalTheory.ConnectionLinear
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConLinR

section Gen
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem contr_lin_right (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {Ξ₁ : WO B.V₀ S → ℂ}
    {Ξ Ξ' : WO S B'.V₀ → ℂ} (c : ℂ) (h₁ : IsThetaFunO ψ B.V₀ S Ξ₁) (hΞ : IsThetaFunO ψ S B'.V₀ Ξ)
    (hΞ' : IsThetaFunO ψ S B'.V₀ Ξ') (u : WO B.A S) (v : WO S B'.A) :
    contr l S vL Ξ₁ (c • Ξ + Ξ') u v = c * contr l S vL Ξ₁ Ξ u v + contr l S vL Ξ₁ Ξ' u v := by
  have iX := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL h₁ hΞ u v
  have iY := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL h₁ hΞ' u v
  simp only [GlobalTheory.Unf.contr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
  rw [integral_add (by simpa only [mul_assoc] using iX.const_mul c) iY, ← integral_const_mul]
  simp only [mul_assoc]

theorem flatFB_lin (hψ : IsStdChar D ψ (-1)) {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (st : StepFB ψ J B)
    {X Y : WO J.W B.V → ℂ} (c : ℂ) (hX : IsThetaFunO ψ J.W B.V X) (hY : IsThetaFunO ψ J.W B.V Y) :
    flatFB st (c • X + Y) = c • flatFB st X + flatFB st Y := by
  rw [(GlobalTheory.FlatAdd.flatFB_add_smul D (GlobalTheory.Unf.Flat.flatLaw D) ψ hψ σ J B st (c • X) Y
    (GlobalTheory.OrientedHeis.theta_smul c hX) hY).1,
    (GlobalTheory.FlatAdd.flatFB_add_smul D (GlobalTheory.Unf.Flat.flatLaw D) ψ hψ σ J B st X X hX hX).2 c]

theorem theta_flatFB {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (st : StepFB ψ J B) {X : WO J.W B.V → ℂ}
    (hX : IsThetaFunO ψ J.W B.V X) : IsThetaFunO ψ J.W₀ B.V₀ (flatFB st X) :=
  (((GlobalTheory.FinPl.flatLaws_all D) ψ (fun _ => True)).2 σ J B st).Heisenberg₂.theta X hX

theorem theta_flatBF {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (st : StepBF ψ B J) {X : WO B.V J.W → ℂ}
    (hX : IsThetaFunO ψ B.V J.W X) : IsThetaFunO ψ B.V₀ J.W₀ (flatBF st X) :=
  (((GlobalTheory.FinPl.flatLaws_all D) ψ (fun _ => True)).1 ρ B J st).Heisenberg₂.theta X hX

end Gen

section Grid
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

theorem fock_lin (p : Pair T) {φ φ' : WO (G.pS p) (G.pT p) → ℂ} (c : ℂ) (hφ : IsThetaFunO W.ψ _ _ φ)
    (hφ' : IsThetaFunO W.ψ _ _ φ') (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.fock p (c • φ + φ') Q = c • W.fock p φ Q + W.fock p φ' Q := by
  simp only [GridData.Weil.fock]
  rw [GlobalTheory.SpecFac.pureTensorO_add W.ψ_std W.θ_is _ _ _ _ (GlobalTheory.OrientedHeis.theta_smul c hφ) hφ' Q,
    GlobalTheory.FiniteFock.pureTensorO_smul]

theorem om_fock_theta (p : Pair T) (hp : p.InRange D.R.m) (g : GA D (G.pS p) × GA D (G.pT p))
    {φ : WO (G.pS p) (G.pT p) → ℂ} (hφ : IsThetaFunO W.ψ _ _ φ) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    IsThetaFunO W.ψ _ _ (W.om p g (W.fock p φ Q)) :=
  (W.om_is p hp).om_pres g _ (GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hφ Q)

end Grid

end GlobalTheory.ConLinR

namespace GlobalTheory.ConLinR
section Main
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem contrLin_one_of (ch : Choice R) : ContrLin ch 1 := by
  intro j hj hjm hm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v
  obtain ⟨a, ha'⟩ := a
  simp only at ha
  subst ha
  have h0 : ¬ (j + 2 * 0 + 2 = D.R.m) := by omega
  have hj' : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨r, hr⟩ := hj; obtain ⟨s, hs⟩ := hm; omega
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, ha'⟩ := by simp
  have hin0 : (Pair.mu t D.R.m j : Pair T).InRange D.R.m := by
    simp only [Pair.InRange, Pair.big, Node.InRange]; omega
  have hin1 : (Pair.mu t D.R.m (j + 1) : Pair T).InRange D.R.m := by
    simp only [Pair.InRange, Pair.big, Node.InRange]; omega
  simp only [conAt, h0, hj', dite_false, dite_true, ↓reduceDIte]
  simp only [fockD, Function.update_of_ne hne, Function.update_self]
  simp only [fock_lin ch.W (Pair.mu t D.R.m (j + 1)) c hφ hφ', map_add (f := _), map_smul]
  erw [flatFB_lin ch.W.ψ_std, contr_lin_right ch.W.ψ_std]
  case hX => exact om_fock_theta ch.W _ hin1 _ hφ _
  case hY => exact om_fock_theta ch.W _ hin1 _ hφ' _
  case h₁ =>
    refine theta_flatBF (B := besAt ch.G hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) _ ?_
    exact om_fock_theta ch.W _ hin0 _ (hΦ ⟨j, by omega⟩) _
  case hΞ =>
    refine theta_flatFB (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) _ ?_
    exact om_fock_theta ch.W _ hin1 _ hφ _
  case hΞ' =>
    refine theta_flatFB (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) _ ?_
    exact om_fock_theta ch.W _ hin1 _ hφ' _

end Main

theorem contrLin_one_big : Big fun ch => GlobalTheory.ConnectionLinear.ContrLin ch 1 :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => contrLin_one_of ch⟩⟩

end GlobalTheory.ConLinR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistCharacterMemTwistFiniteValueProductSubgroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XiVals

theorem xi_mem : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (x : (AE D)ˣ),
    Circle.toUnits (R.toLevCh.xi t x) ∈ xiVals R.toLevCh t :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS _ _ _ t x =>
    GlobalTheory.ColVac.xi_mem_xiVals hS.core.lev t x⟩⟩

end GlobalTheory.XiVals

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductFunctionEqOfLocalIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem prodRel_map {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (T : ∀ l, (X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, T l (g i l) (y l) = 0 := by
  have hkey : ∀ l, ∃ (s : Finset (X l)) (E : X l → X l → ℂ), (∀ x, E x ∈ (⊤ : Submodule ℂ (X l → ℂ))) ∧
      ∀ u ∈ S.image (fun i => g i l), u = ∑ x ∈ s, u x • E x := fun l =>
    GlobalTheory.finset_functions_recovered_from_values ⊤ _ (fun _ _ => Submodule.mem_top)
  choose s E _ hE using hkey
  have h1 : ∀ i ∈ S, ∏ l, T l (g i l) (y l) =
      ∑ ξ ∈ Fintype.piFinset s, (∏ l, g i l (ξ l)) * ∏ l, T l (E l (ξ l)) (y l) := by
    intro i hi
    have h2 : ∀ l, T l (g i l) (y l) = ∑ x ∈ s l, g i l x * T l (E l x) (y l) := by
      intro l
      conv_lhs => rw [hE l (g i l) (Finset.mem_image_of_mem _ hi)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finset.sum_apply]
    simp only [h2]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun i hi => by rw [h1 i hi, Finset.mul_sum], Finset.sum_comm]
  refine Finset.sum_eq_zero fun ξ _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, h ξ, zero_mul]

theorem prodRel_allSome {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, f i l (y l) = 0 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  choose T hT using fun l => (hf i₀ hi₀ l).1
  rw [← prodRel_map S x g T h y]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [fun l => (hf i hi l).2 _ (hT l)]

theorem prodRel_allSome₂ {ι κ I : Type} [Fintype ι] [Fintype κ] {X Y : ι → Type} {X' Y' : κ → Type} (S : Finset I) (x : I → ℂ)
    (g : I → ∀ l, X l → ℂ) (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (g' : I → ∀ l, X' l → ℂ) (f' : I → ∀ l, Y' l → ℂ) (Q' : ∀ l, ((X' l → ℂ) →ₗ[ℂ] (Y' l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (hf' : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q' l) fun T => f' i l = T (g' i l))
    (h : ∀ (z : ∀ l, X l) (z' : ∀ l, X' l), ∑ i ∈ S, x i * ((∏ l, g i l (z l)) * ∏ l, g' i l (z' l)) = 0)
    (y : ∀ l, Y l) (y' : ∀ l, Y' l) :
    ∑ i ∈ S, x i * ((∏ l, f i l (y l)) * ∏ l, f' i l (y' l)) = 0 := by
  simp only [← mul_assoc]
  refine prodRel_allSome S (fun i => x i * ∏ l, f i l (y l)) g' f' Q' hf' (fun z' => ?_) y'
  have := prodRel_allSome S (fun i => x i * ∏ l, g' i l (z' l)) g f Q hf (fun z => by
    rw [← h z z']
    exact Finset.sum_congr rfl fun i _ => by ring) y
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem unfolded_eq_of_local_eq : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → ∀ (α : Type) (SA : Finset α) (xA : α → ℂ) (F : α → ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ) (Gd : α → ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) → ℂ) (fr : α → SchRow ch.G) (fd : α → SchDown ch.G t), (∀ a ∈ SA, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (F a i) (fr a i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (Gd a j) (fd a j)) → (∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ SA, xA a * (∏ i, F a i (x i)) * ∏ j, Gd a j (y j)) → ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R Fc _ ch _ _ hcon t e _ τ φ hτ α SA xA F Gd fr fd hA hloc M hM P h u y
  have key := hcon t M hM P h ((SchRow ch.G × SchDown ch.G t) ⊕ α) (τ.support.disjSum SA)
    (Sum.elim (fun d => τ d) fun a => -xA a) (Sum.elim (fun d => d.1) fr) (Sum.elim (fun d => d.2) fd) ?_ ?_ u y
  · rw [Finset.sum_disjSum] at key
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
    exact add_neg_eq_zero.mp key
  · intro i hi j
    have hv := (ch.rm.vT_is t D.R.m j le_rfl j.2).2.theta
    rcases i with d | a
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hτ d (by simpa using hi)).2 j).2 hv
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hA a (by simpa using hi)).2 j).2 hv
  · intro y v
    refine prodRel_allSome₂ (τ.support.disjSum SA) (Sum.elim (fun d => τ d) fun a => -xA a)
      (Sum.elim (fun d => (φ d).1) F) (Sum.elim (fun d => d.1) fr)
      (fun i => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) (ch.G.latS (.chi i D.R.m : Pair T) : Set _)
          (ch.G.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) 1 (ch.rm.vX i D.R.m))
      (Sum.elim (fun d => (φ d).2) Gd) (Sum.elim (fun d => d.2) fd)
      (fun j => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) (ch.G.latS (.mu t D.R.m j : Pair T) : Set _)
          (ch.G.latT (.mu t D.R.m j : Pair T) : Set _) fun _ => True) 1 (ch.rm.vT D.R.m j)) ?_ ?_ ?_ y v
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).1 l).2
      · exact ((hA a (by simpa using hi)).1 l).2
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).2 l).2
      · exact ((hA a (by simpa using hi)).2 l).2
    · intro z z'
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, ← mul_assoc]
      exact add_neg_eq_zero.mpr (hloc z z')

end GlobalTheory.LocAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointMovesRowLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl

noncomputable section
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseTiltMove

variable {D : D7}

theorem incA_inj : Function.Injective (incA D) := by
  haveI : Nontrivial (AF D.host.F) :=
    (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective

theorem incA_apply (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem mulVec_latV_of_rat (S : HSp D) (γ : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (L M : Lat S)
    (hLM : ∀ x ∈ L, γ *ᵥ x ∈ M) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : y ∈ latV S L P) :
    γ.map (incA D) *ᵥ y ∈ latV S M P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, hαP, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨α, hα, hαP, 1, rfl, γ *ᵥ x, hLM x hx, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, incA_apply, one_mul, Algebra.TensorProduct.tmul_mul_tmul,
      ← TensorProduct.tmul_sum]
  | zero => simp only [Matrix.mulVec_zero]; exact (latV S M P).zero_mem
  | add u v _ _ hu hv => rw [Matrix.mulVec_add]; exact (latV S M P).add_mem hu hv
  | neg u _ hu => rw [Matrix.mulVec_neg]; exact (latV S M P).neg_mem hu

theorem exists_rat_of_GQ (S : HSp D) (δ : GA D S) (h : δ ∈ GQ S) :
    ∃ γ : GL (Fin S.rank) D.host.E, mt S δ = γ.val.map (incA D) ∧ mt S δ⁻¹ = (γ⁻¹).val.map (incA D) := by
  obtain ⟨γ, -, hγ⟩ := h
  have e : matHom S δ = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ := hγ.symm
  refine ⟨γ, ?_, ?_⟩
  · show (matHom S δ).val = _
    rw [e]; rfl
  · show (matHom S δ⁻¹).val = _
    rw [map_inv, e, ← map_inv]; rfl

theorem moves_of_rat (S : HSp D) (δ : GA D S) (γ γ' : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (h : mt S δ = γ.map (incA D)) (h' : mt S δ⁻¹ = γ'.map (incA D)) (L M : Lat S)
    (hLM : ∀ x ∈ L, γ *ᵥ x ∈ M) (hML : ∀ x ∈ M, γ' *ᵥ x ∈ L) (P : Pl D → Prop) : Moves S δ L M P := by
  intro y _
  refine ⟨fun hy => h ▸ mulVec_latV_of_rat S γ L M hLM P y hy, fun hy => ?_⟩
  have e : mt S δ⁻¹ *ᵥ (mt S δ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.FinPl.PlacesAdeles.mt_mul, inv_mul_cancel, GlobalTheory.FinPl.PlacesAdeles.mt_one,
      Matrix.one_mulVec]
  rw [← e, h']
  exact mulVec_latV_of_rat S γ' M L hML P _ hy

theorem moves_of_isFinOf (S : HSp D) {δ b : GA D S} (hb : IsFinOf δ b) (L M : Lat S)
    (h : Moves S δ L M (fun _ => True)) : Moves S b L M (fun _ => True) := by
  obtain ⟨-, a, ha, hab⟩ := hb
  have hb' : b = a⁻¹ * δ := by rw [← hab, inv_mul_cancel_left]
  intro y hy
  have hy' := GlobalTheory.FinPl.PlacesAdeles.supp_mulVec S _ δ hy
  rw [hb', GlobalTheory.FinPl.PlacesAdeles.mt_mul, ← Matrix.mulVec_mulVec,
    GlobalTheory.FinPl.PlacesAdeles.mulVec_off (GlobalTheory.FinPl.SuppTwoAsm.ginf_le_grpOff S _ (inv_mem ha)) hy']
  exact h y hy

theorem moves_one (S : HSp D) (L : Lat S) (P : Pl D → Prop) : Moves S 1 L L P := by
  intro y _
  rw [GlobalTheory.FinPl.PlacesAdeles.mt_one, Matrix.one_mulVec]

theorem sumLat_mulVec {n k c : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (M₀ : Matrix (Fin n) (Fin k) D.host.E)
    (Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (a : Matrix (Fin n) (Fin c) D.host.E)
    (𝔟 𝔟' : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (t : Fin c → D.host.E) (hM : γ * M₀ = M₀)
    (ha : γ * a = a * diagonal t) (ht : ∀ p, ∀ u ∈ 𝔟 p, t p * u ∈ 𝔟' p) :
    ∀ x ∈ sumLat M₀ Λ a 𝔟, γ *ᵥ x ∈ sumLat M₀ Λ a 𝔟' := by
  rintro _ ⟨y, hy, u, hu, rfl⟩
  refine ⟨y, hy, fun p => t p * u p, fun p => ht p _ (hu p), ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hM, Matrix.mulVec_mulVec, ha, ← Matrix.mulVec_mulVec]
  congr 2
  funext p
  exact Matrix.mulVec_diagonal _ _ _

section Grid

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem lat_grid (j : ℕ) (h1 : 1 ≤ j) (h : j < D.R.m) :
    G.Λ (.grid D.R.m j) = (G.rowDec j h).lat (G.Λ (.top j)) (stairId D.host.AA D.host.AAbar (D.R.m - 1 - j)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact G.sp.rowLat j' h

variable {G}

theorem tilt_cols {j : ℕ} (hj : j < D.R.m) (hodd : Odd j) {δ : GA D (G.V (.grid D.R.m j))} (hδ : IsTilt G j δ)
    (γ : Matrix (Fin (G.V (.grid D.R.m j)).rank) (Fin (G.V (.grid D.R.m j)).rank) D.host.E)
    (hγ : mt _ δ = γ.map (incA D)) :
    γ * frameMat _ _ (G.rowDec j hj).ι = frameMat _ _ (G.rowDec j hj).ι ∧
      γ * (G.rowDec j hj).a = (G.rowDec j hj).a * diagonal (GlobalTheory.RowShape.tiltSc D j) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, D.R.m - 1 - j = 2 * σ := by
    obtain ⟨a, ha⟩ := D.R.m_even; obtain ⟨b, hb⟩ := hodd; exact ⟨(D.R.m - 1 - j) / 2, by omega⟩
  obtain ⟨h0, he, he'⟩ := hδ.2.2 σ hj hσ
  rw [hγ, ← Matrix.map_mul] at h0 he he'
  have h0 := Matrix.map_injective incA_inj h0
  have he := Matrix.map_injective incA_inj he
  have he' := Matrix.map_injective incA_inj he'
  refine ⟨h0, Matrix.ext fun k p => ?_⟩
  rw [Matrix.mul_diagonal]
  by_cases hp : 2 * p.1 < D.R.m - 1 - j
  · have := congrFun (congrFun he k) ⟨p.1, by omega⟩
    simp only [Matrix.mul_diagonal] at this
    have e1 : (γ * (rowJac G j hj σ hσ).e) k ⟨p.1, by omega⟩ = (γ * (G.rowDec j hj).a) k p := rfl
    have e2 : (rowJac G j hj σ hσ).e k ⟨p.1, by omega⟩ = (G.rowDec j hj).a k p := rfl
    rw [← e1, this, e2]
    simp [GlobalTheory.RowShape.tiltSc, hodd, hp]
  · have := congrFun (congrFun he' k) ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩
    simp only [Matrix.mul_diagonal] at this
    have hq : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) (⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ : Fin σ)).rev = p :=
      Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    have e1 : (γ * (rowJac G j hj σ hσ).e') k ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ = (γ * (G.rowDec j hj).a) k p := by
      simp only [Matrix.mul_apply, GlobalTheory.RowUnf.rowJac, GlobalTheory.RowUnf.jacDec, Matrix.submatrix_apply, id_eq, hq]
    have e2 : (rowJac G j hj σ hσ).e' k ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ = (G.rowDec j hj).a k p := by
      simp only [GlobalTheory.RowUnf.rowJac, GlobalTheory.RowUnf.jacDec, Matrix.submatrix_apply, id_eq, hq]
    rw [← e1, this, e2]
    simp [GlobalTheory.RowShape.tiltSc, hodd, hp]

end Grid

section Main

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem tiltSc_ne_zero (j : ℕ) (p : Fin (D.R.m - 1 - j)) : GlobalTheory.RowShape.tiltSc D j p ≠ 0 := by
  unfold GlobalTheory.RowShape.tiltSc
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact star_ne_zero.2 (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact one_ne_zero

theorem moves_idx (t : T) (B : Frames G) (b : Pts G) (hb : IsBase t B b) (j : ℕ) (hj : j ∈ idx D) :
    Moves _ (b j) (G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN G j) fun _ => True := by
  have hj' : 1 ≤ j ∧ j < 1 + (D.R.m - 2) := List.mem_range'_1.1 hj
  have hjm : j < D.R.m := by omega
  obtain ⟨δ, hδ, hfin⟩ := hb.2.1 j hj
  refine moves_of_isFinOf _ hfin _ _ ?_
  have hN : GlobalTheory.RowShape.rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (GlobalTheory.RowShape.rowId D j) := by
    unfold GlobalTheory.RowShape.rowN; rw [dite_eq_left hjm]
  rw [lat_grid G j hj'.1 hjm, hN]
  by_cases hodd : Odd j
  · obtain ⟨γ, hγ, hγ'⟩ := exists_rat_of_GQ _ δ hδ.1
    obtain ⟨h0, ha⟩ := tilt_cols hjm hodd hδ γ.val hγ
    set t := GlobalTheory.RowShape.tiltSc D j
    have hinv : (γ⁻¹).val * γ.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h0' : (γ⁻¹).val * frameMat _ _ (G.rowDec j hjm).ι = frameMat _ _ (G.rowDec j hjm).ι := by
      conv_lhs => rw [← h0]
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hdd : diagonal t * diagonal (fun p => (t p)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal,
        show (fun p => t p * (t p)⁻¹) = fun _ => (1 : D.host.E) from funext fun p => mul_inv_cancel₀ (tiltSc_ne_zero j p)]
      exact Matrix.diagonal_one
    have ha' : (γ⁻¹).val * (G.rowDec j hjm).a = (G.rowDec j hjm).a * diagonal (fun p => (t p)⁻¹) := by
      calc (γ⁻¹).val * (G.rowDec j hjm).a
          = (γ⁻¹).val * ((G.rowDec j hjm).a * (diagonal t * diagonal (fun p => (t p)⁻¹))) := by
            rw [hdd, Matrix.mul_one]
        _ = (γ⁻¹).val * (γ.val * (G.rowDec j hjm).a) * diagonal (fun p => (t p)⁻¹) := by
            simp only [ha, Matrix.mul_assoc]
        _ = _ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine moves_of_rat _ δ γ.val (γ⁻¹).val hγ hγ' _ _ ?_ ?_ _
    · refine sumLat_mulVec _ _ _ _ _ _ t h0 ha fun p u hu => ?_
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hu
    · refine sumLat_mulVec _ _ _ _ _ _ (fun p => (t p)⁻¹) h0' ha' fun p u hu => ?_
      obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hu
      rw [← mul_assoc, inv_mul_cancel₀ (tiltSc_ne_zero j p), one_mul]
      exact hz
  · have h1 : δ = 1 := hδ.2.1 (Nat.not_odd_iff_even.1 hodd)
    subst h1
    have hI : GlobalTheory.RowShape.rowId D j = stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) := by
      funext p
      simp [GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc, hodd]
    rw [hI]
    exact moves_one _ _ _

theorem moves_rowN (t : T) (B : Frames G) (b : Pts G) (hb : IsBase t B b) (j : ℕ) (h1 : 1 ≤ j) (hm : j ≤ D.R.m) :
    Moves _ (b j) (G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN G j) fun _ => True := by
  by_cases hj : j ∈ idx D
  · exact moves_idx t B b hb j hj
  rw [hb.2.2 j (by omega) hj]
  by_cases hjm : j < D.R.m
  · have hc : D.R.m - 1 - j = 0 := by
      have : ¬ (1 ≤ j ∧ j < 1 + (D.R.m - 2)) := fun h => hj (List.mem_range'_1.2 h)
      omega
    have hN : GlobalTheory.RowShape.rowN G j = G.Λ (.grid D.R.m j) := by
      unfold GlobalTheory.RowShape.rowN
      rw [dite_eq_left hjm, lat_grid G j h1 hjm]
      congr 1
      funext p
      exact absurd p.2 (by omega)
    rw [hN]
    exact moves_one _ _ _
  · have hN : GlobalTheory.RowShape.rowN G j = G.Λ (.grid D.R.m j) := by
      unfold GlobalTheory.RowShape.rowN; rw [dite_eq_right hjm]
    rw [hN]
    exact moves_one _ _ _

end Main

theorem base_moves_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → ∀ j, 1 ≤ j → j ≤ D.R.m → GlobalTheory.FinPl.Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN ch.G j) fun _ => True := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t b hb j h1 hm
  exact moves_rowN t ch.S.B b hb j h1 hm

end GlobalTheory.BaseTiltMove
end
end

