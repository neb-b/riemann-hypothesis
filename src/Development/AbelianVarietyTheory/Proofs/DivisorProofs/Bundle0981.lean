module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
section
noncomputable section

namespace GlobalTheory.AdTh.CoefExt

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (φ : K →+* K')
  {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]

theorem map_actP (B : I → GL (Fin n) K) (F : Pol K I n) :
    MvPolynomial.map φ (actP lam B F) = actP lam (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) := by
  have h1 : (MvPolynomial.map φ).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc φ (B τ))).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map φ (trAct B F) = trAct (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) :=
    congrArg (fun ψ : Pol K I n →+* Pol K' I n => ψ F) h1
  have h3 : φ (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc φ (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

def up (v : VV K lam) : VV K' lam := ⟨MvPolynomial.map φ (v : Pol K I n), GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ v.2⟩

theorem up_sum (a : VVIdx lam → K) (v : VVIdx lam → VV K lam) :
    up φ lam (∑ j, a j • v j) = ∑ j, φ (a j) • up φ lam (v j) := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [up, Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eq_C_mul, map_mul, map_C]

theorem exists_coord (v : VV K' lam) : ∃ a : VVIdx lam → K', v = ∑ j, a j • up φ lam (bVV K lam j) := by
  have hv : v ∈ Submodule.span K' (Set.range (bVV K' lam)) := by rw [(bVV K' lam).span_eq]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc φ lam j
    refine ⟨fun k => φ ((bVV K lam).repr ⟨F, hF⟩ k), ?_⟩
    rw [← up_sum, (bVV K lam).sum_repr]
    exact Subtype.ext ((bVV_coe _ _ _).trans hj)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp [← Finset.sum_add_distrib, add_smul]⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨fun j => c * a j, by simp [Finset.smul_sum, mul_smul]⟩

theorem up_rhoVr {E : Type} [Field E] [NumberField E] [NumberField K] [NumberField K'] (emb : I → E →+* K)
    (g : GL (Fin n) E) (v : VV K lam) :
    up φ lam (rhoVr emb lam g v) = rhoVr (fun τ => φ.comp (emb τ)) lam g (up φ lam v) := by
  apply Subtype.ext
  show MvPolynomial.map φ (actP lam (invTrK (embGL emb g)) (v : Pol K I n)) =
    actP lam (invTrK (embGL (fun τ => φ.comp (emb τ)) g)) (MvPolynomial.map φ (v : Pol K I n))
  rw [map_actP]
  rfl

variable {φ lam} {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

theorem equivariant (hE : ∀ v, c' (up φ lam v) = c₀ v) (T : W →ₗ[ℂ] W) (S : VV K lam →ₗ[K] VV K lam)
    (S' : VV K' lam →ₗ[K'] VV K' lam) (hS : ∀ v, up φ lam (S v) = S' (up φ lam v)) (hT : ∀ v, c₀ (S v) = T (c₀ v))
    (v : VV K' lam) : c' (S' v) = T (c' v) := by
  obtain ⟨a, rfl⟩ := exists_coord φ lam v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_smulₛₗ, ← hS, hE, hT, RingHom.id_apply]

theorem span_top (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hs : Submodule.span ℂ (Set.range fun j => c₀ (bVV K lam j)) = ⊤) : Submodule.span ℂ (Set.range c') = ⊤ := by
  refine top_le_iff.1 (hs ▸ Submodule.span_mono ?_)
  rintro _ ⟨j, rfl⟩
  exact ⟨_, hE _⟩

theorem linearIndependent (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hli : LinearIndependent ℂ fun j => c₀ (bVV K lam j)) {m : ℕ} (b : Fin m → VV K' lam) (hb : LinearIndependent K' b) :
    LinearIndependent ℂ fun j => c' (b j) := by
  classical
  letI : Algebra K' ℂ := σ'.toAlgebra
  choose a ha using fun j => exists_coord φ lam (b j)
  have h1 : LinearIndependent K' a := by
    refine LinearIndependent.of_comp (Fintype.linearCombination K' fun k => up φ lam (bVV K lam k)) ?_
    convert hb using 1
    funext j
    rw [ha j]
    simp [Fintype.linearCombination_apply]
  have h2 : LinearIndependent ℂ fun j => algebraMap K' ℂ ∘ a j := linearIndependent_algebraMap_comp_iff.2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k))
    (LinearMap.ker_eq_bot'.2 fun g hg => funext (Fintype.linearIndependent_iff.1 hli g (by simpa [Fintype.linearCombination_apply] using hg)))
  have e : (fun j => c' (b j)) = ⇑(Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k)) ∘ fun j => algebraMap K' ℂ ∘ a j := by
    funext j
    rw [ha j]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, hE, Function.comp_apply, Fintype.linearCombination_apply]
    rfl
  rw [e]
  exact h3

theorem pairVr_extremal {E : Type} [Field E] [NumberField E] [NumberField K] [StarRing K] (emb : I → E →+* K)
    (v : VV K lam) (hv : (v : Pol K I n) = ten fun τ => extremal K n (lam τ)) : pairVr emb lam 1 v v = 1 := by
  have hG : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    simp [gramKd]
  have h := pairingExtremal_holds K I n lam (fun _ => 1) 1 (fun τ => by simp)
  rw [polyAction_one₂] at h
  rw [pairVr, pairK_apply, hG, hv, h]

end GlobalTheory.AdTh.CoefExt

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem inner_of_coefTie {D : D7} {V : HSp D} {C : Bridge.CoefDat D V} {S : Formalism.L2.DIV.CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ : J →* ℂˣ} {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : Formalism.L2.DIV.VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    (h : Bridge.CoefTie V C P lam c0 pair nab del) (v w : Formalism.L2.DIV.VV D.what₂.LL lam) :
    inner ℂ (c0 v) (c0 w) = D.what₂.embLL (pair v w) := by
  obtain ⟨e, -, he, hp, -⟩ := h
  have hi := P.coef_pair (e.symm v) (e.symm w)
  rwa [he, he, ← hp, e.apply_symm_apply, e.apply_symm_apply] at hi


set_option maxHeartbeats 800000 in
theorem coefMap_norm_equivariant_basis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ‖O.c0' O.hw‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, O.c0' (rhoM O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v) = (R.cV i).ρ γ (O.c0' v)) ∧ Submodule.span ℂ (Set.range O.c0') = ⊤ ∧ ∀ (m : ℕ) (b : Fin m → VsV D i O.c'.F), LinearIndependent O.c'.F b → LinearIndependent ℂ (fun j => O.c0' (b j)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hσ := hP.lift.field
  have hE : ∀ v, O.c0' (CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT.mapL i
  refine ⟨?_, ?_, CoefExt.span_top (W := (R.cV i).W) hE h3,
    fun m b hb => CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb⟩
  · have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hP.lift.std
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hP.lift.std.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : CoefExt.up O.jL (lamV D i) v = O.hw := by
      apply Subtype.ext
      have hw := hP.io.1
      unfold hwOK at hw
      refine Eq.trans ?_ hw.symm
      show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _
      rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      exact Formalism.L2.DIV.map_extremal _ _ _
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := inner_of_coefTie (hT.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [← hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  · intro γ γE hγ v
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    have hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ) :=
      funext fun τ => (embV_eq_embF O.c' O.jL hσ τ).symm
    rw [rhoM, dite_eq_left hu, hγE, hemb]
    exact CoefExt.equivariant (W := (R.cV i).W) hE ((R.cV i).ρ γ) (Formalism.L2.DIV.rhoVr (labLL D) (lamV D i) γE) _
      (CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE) (h1 γ γE hγ) v

end GlobalTheory.AdTh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CofinitePlacesRealizePrimes
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain Rat.HeightOneSpectrum

theorem exists_finset_forall_prime_awayP_padic :
    ∀ (p : ℕ) [Fact p.Prime] (P : AwayP p → Prop), (∀ᶠ w in Filter.cofinite, P w) →
    ∃ S : Finset ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ w : AwayP p, P w ∧ Nonempty (w.1.adicCompletion ℚ ≃+* ℚ_[ℓ]) := by
  intro p _ P hP
  have hfin : {w : AwayP p | ¬ P w}.Finite := hP
  refine ⟨insert p (hfin.toFinset.image fun w => ((primesEquiv (R := ℤ) w.1 : Nat.Primes) : ℕ)), ?_⟩
  intro ℓ hℓ hS
  have hℓp : ℓ ≠ p := fun h => hS (by simp [h])
  let q : Nat.Primes := ⟨ℓ, hℓ.out⟩
  let v : HeightOneSpectrum ℤ := (primesEquiv (R := ℤ)).symm q
  have hv : ((primesEquiv (R := ℤ) v : Nat.Primes) : ℕ) = ℓ := by
    show ((primesEquiv (R := ℤ) ((primesEquiv (R := ℤ)).symm q) : Nat.Primes) : ℕ) = ℓ
    rw [Equiv.apply_symm_apply]
  have hne : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have h1 := span_natGenerator (R := ℤ) v
    have h2 : natGenerator v = ℓ := hv
    rw [h, h2, Ideal.map_span] at h1
    simp only [Set.image_singleton, map_natCast] at h1
    have h3 : (ℓ : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (h1 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (p : ℤ) ∣ (ℓ : ℤ) := Ideal.mem_span_singleton.1 (h1.symm ▸ Ideal.mem_span_singleton_self _)
    exact hℓp (Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 h3) (Int.natCast_dvd_natCast.1 h4))
  refine ⟨⟨v, hne⟩, ?_, ?_⟩
  · by_contra hw
    apply hS
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨v, hne⟩, hfin.mem_toFinset.2 hw, hv⟩)
  · exact ⟨((Padic.adicCompletionEquiv ℤ q).symm : _ ≃+* ℚ_[(q : ℕ)])⟩

end GlobalTheory.FinClsLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvTopOrRat
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem coinv_top_or_rat (P Q R S : ℕ) (x : ℂ) :
    coinv P Q R S x = ⊤ ∨ ∃ x' : ℚ, coinv P Q R S x = coinv P Q R S (x' : ℂ) := by
  by_cases hx : ∃ x' : ℚ, x = x'
  · obtain ⟨x', rfl⟩ := hx
    exact Or.inr ⟨x', rfl⟩
  push_neg at hx
  by_cases hI : IsEmpty (Ix P Q)
  · right
    refine ⟨0, ?_⟩
    unfold coinv
    congr 1
    ext g
    simp [Matrix.trace, Finset.univ_eq_empty]
  · left
    rw [not_isEmpty_iff] at hI
    obtain ⟨a⟩ := hI
    let K : Subring ℂ := (Rat.castHom ℂ).range
    have hxK : x ∉ K := by
      rintro ⟨q, hq⟩
      exact hx q hq.symm
    have hsign : ∀ c : Ix R S, lineSign a c ∈ K := by
      intro c
      rcases a with a | a <;> rcases c with c | c <;> simp only [lineSign] <;>
        first | exact K.one_mem | exact K.neg_mem K.one_mem
    have hc : ∀ α : Ln P Q R S →₀ ℕ, (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) ∈ K := by
      intro α
      refine K.sum_mem fun c _ => K.mul_mem (hsign c) (K.add_mem (natCast_mem K _) ?_)
      exact RingHom.mem_range.mpr ⟨1 / 2, by simp⟩
    have hmon : ∀ α : Ln P Q R S →₀ ℕ, (MvPolynomial.monomial α (1 : ℂ) : Pol P Q R S) ∈ coinv P Q R S x := by
      intro α
      have hne : (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x ≠ 0 := by
        intro h
        apply hxK
        rw [sub_eq_zero] at h
        rw [← h]
        exact hc α
      have hg : fockAct1 P Q R S (Eab a a) (MvPolynomial.monomial α 1) -
          (x * (Eab a a : Mat P Q).trace) • MvPolynomial.monomial α 1 ∈ coinv P Q R S x :=
        Submodule.subset_span ⟨Eab a a, _, rfl⟩
      have htr : (Eab a a : Mat P Q).trace = 1 := by simp [Eab]
      rw [cartan1, htr, mul_one, ← sub_smul] at hg
      have h2 := (coinv P Q R S x).smul_mem ((∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x)⁻¹ hg
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    rw [eq_top_iff]
    intro f _
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    have he : (MvPolynomial.monomial α (AddMonoidAlgebra.coeff f α) : Pol P Q R S) =
        AddMonoidAlgebra.coeff f α • MvPolynomial.monomial α 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [he]
    exact (coinv P Q R S x).smul_mem _ (hmon α)

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCentralizerTranslate
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.TorusNorm

theorem exists_compact_mod_sim (Z S : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z]
    [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z]
    [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [SigmaCompactSpace S]
    [T2Space S] (hZ : ∀ a b : Z, a * b = b * a) (hS : ∀ a b : S, a * b = b * a)
    (τ : Z →* Z) (hτc : Continuous τ) (hτi : ∀ z, τ (τ z) = z)
    (hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s)
    (ι : S →* Z) (hιc : Continuous ι) (hτι : ∀ a, τ (ι a) = ι a)
    (hU : ∃ U ∈ nhds (1 : S), ∀ a ∈ U, a * a = 1 → a = 1) (D : Set Z) (hD : IsCompact D) :
    ∃ B : Set Z, IsCompact B ∧ ∀ (z : Z) (a : S), τ z * z * (ι a)⁻¹ ∈ D →
      ∃ u : Z, ∃ l : S, τ u * u = ι l ∧ ∃ b ∈ B, z = u * b := by
  let T : Z × S →* Z × S :=
    { toFun := fun h => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
      map_one' := by simp
      map_mul' := fun h k => by
        ext
        · show τ (h.1 * k.1) * (ι (h.2 * k.2))⁻¹ = τ h.1 * (ι h.2)⁻¹ * (τ k.1 * (ι k.2)⁻¹)
          rw [map_mul, map_mul, _root_.mul_inv_rev, hZ (ι k.2)⁻¹ (ι h.2)⁻¹]
          simp only [mul_assoc]
          congr 1
          rw [← mul_assoc, ← mul_assoc, hZ (ι h.2)⁻¹ (τ k.1)]
        · show (h.2 * k.2)⁻¹ = h.2⁻¹ * k.2⁻¹
          rw [_root_.mul_inv_rev, hS] }
  have hT : ∀ h, T h = (τ h.1 * (ι h.2)⁻¹, h.2⁻¹) := fun h => rfl
  have hcomm : ∀ a b : Z × S, a * b = b * a := fun a b => Prod.ext (hZ _ _) (hS _ _)
  have hTc : Continuous T := by
    show Continuous fun h : Z × S => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
    exact ((hτc.comp continuous_fst).mul (hιc.comp continuous_snd).inv).prodMk continuous_snd.inv
  have hTi : ∀ h, T (T h) = h := by
    intro h
    rw [hT, hT]
    ext
    · simp only [map_mul, map_inv, hτi, hτι, inv_inv]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    · simp
  obtain ⟨W, hW, hWs⟩ := hsq
  obtain ⟨U, hU1, hUs⟩ := hU
  have hsqT : ∃ W' ∈ nhds (1 : Z × S), ∀ s ∈ W', T s = s → ∃ r : Z × S, T r = r ∧ r * r = s := by
    refine ⟨W ×ˢ U, prod_mem_nhds hW hU1, fun s hs hTs => ?_⟩
    have h2 : s.2⁻¹ = s.2 := congrArg Prod.snd hTs
    have ha : s.2 = 1 := hUs _ hs.2 (by
      calc s.2 * s.2 = s.2 * s.2⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _)
    have h1 : τ s.1 * (ι s.2)⁻¹ = s.1 := congrArg Prod.fst hTs
    rw [ha, map_one, inv_one, mul_one] at h1
    obtain ⟨r, hr, hrr⟩ := hWs _ hs.1 h1
    refine ⟨(r, 1), ?_, ?_⟩
    · rw [hT]; simp [hr]
    · ext
      · exact hrr
      · simp [ha]
  haveI : T2Space (Z × S) := inferInstance
  obtain ⟨B, hB, hBs⟩ := GlobalTheory.InvolutionNorm.exists_compact_mod_kernel (Z × S) hcomm T hTc hTi hsqT
    (D ×ˢ {1}) (hD.prod isCompact_singleton)
  refine ⟨Prod.fst '' B, hB.image continuous_fst, fun z a hz => ?_⟩
  have hmem : T (z, a) * (z, a) ∈ D ×ˢ ({1} : Set S) := by
    rw [hT]
    refine ⟨?_, ?_⟩
    · show τ z * (ι a)⁻¹ * z ∈ D
      rw [mul_assoc, hZ (ι a)⁻¹ z, ← mul_assoc]; exact hz
    · show a⁻¹ * a = 1
      exact inv_mul_cancel a
  obtain ⟨t, ht, b, hb, hzb⟩ := hBs _ hmem
  refine ⟨t.1, t.2, ?_, b.1, ⟨b, hb, rfl⟩, congrArg Prod.fst hzb⟩
  have h1 : τ t.1 * (ι t.2)⁻¹ * t.1 = 1 := congrArg Prod.fst ht
  rw [mul_assoc, hZ _ t.1, ← mul_assoc] at h1
  exact mul_inv_eq_one.1 h1

end GlobalTheory.OrbFinAf.TorusNorm

namespace GlobalTheory.OrbFinAf.TorusNorm

end GlobalTheory.OrbFinAf.TorusNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositeCutOperatorsProductLocalCellsMirabolicStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  first | exact @GlobalTheory.JSW.CutProd.cut_prod_mirS | exact GlobalTheory.JSW.CutProd.cut_prod_mirS | (intros; apply GlobalTheory.JSW.CutProd.cut_prod_mirS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E)

theorem cA_cA (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    show Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
    simp [hσ]


variable (F E) in
theorem topAE : IsTopologicalRing (AE F E) ∧ LocallyCompactSpace (AE F E) ∧ SecondCountableTopology (AE F E) ∧
    T2Space (AE F E) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact ⟨inferInstance, e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology, e.isEmbedding.t2Space⟩

theorem continuous_cA : Continuous (cA σ) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI := (topAE F E).1
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem topUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧
      T2Space (UA σ J) := by
  obtain ⟨h1, h2, h3, h4⟩ := topAE F E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hs : Continuous (cA σ) := continuous_cA σ
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs))
      continuous_const
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology,
    inferInstanceAs (T2Space (UG (cA σ) (incM F J)))⟩

end GlobalTheory.LeviModulus

end
end

