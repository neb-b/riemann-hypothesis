module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefMapNormEquivariantBasisOfPre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.SeriesTie

noncomputable section

namespace GlobalTheory.ChoiceAdm

open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem star_eq_conj (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

abbrev cnj (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

theorem cnj_coe (x : 𝓞 D.host.E) : ((cnj D x : 𝓞 D.host.E) : D.host.E) = D.host.conj x := rfl

theorem isConjPl_of_lev {P P' : Pl D.host.E} (h : Lev.IsConjPl P P') : IsConjPl D.host P P' := by
  have hle : P.asIdeal ≤ P'.asIdeal.comap (cnj D) := fun c hc => by
    obtain ⟨c', h1, h2⟩ := h c hc
    have e : cnj D c = c' := RingOfIntegers.ext (by rw [cnj_coe, h2, star_eq_conj])
    rw [Ideal.mem_comap, e]
    exact h1
  have heq := P.isMaximal.eq_of_le (Ideal.comap_ne_top _ P'.isPrime.ne_top) hle
  intro x y hxy
  have e : y = cnj D x := RingOfIntegers.ext hxy
  rw [e, ← Ideal.mem_comap, ← heq]

theorem not_lev_self {P : Pl D.host.E} (h : IsSplitPl D.host P) : ¬ Lev.IsConjPl P P := fun hc =>
  GlobalTheory.SeriesTie.ne_of_split h (isConjPl_of_lev hc) rfl

theorem exists_idem {P : Pl D.host.E} (h : IsSplitPl D.host P) : ∃ e, IsIdemAt e P := by
  refine GlobalTheory.MovedIdem.exists_isIdemAt P fun hP => ?_
  obtain ⟨x, hx, hy⟩ := h
  refine hy (cnj D x) rfl ?_
  rw [← hP]
  exact Ideal.subset_span ⟨x, hx, by
    change ((cnj D x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E)
    rw [cnj_coe, star_eq_conj]⟩

theorem lev_of_eq_cA {i j : Pl D.host.E} {a b : Formalism.L2.Theta.AE D} (ha : IsIdemAt a i) (hb : IsIdemAt b j)
    (e : a = cA D b) : Lev.IsConjPl j i := by
  have hc : Lev.IsConjPl j (GlobalTheory.IdemSupport.cP j) := fun c hc =>
    ⟨GlobalTheory.IdemSupport.cO D c, by
      show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) ∈ j.asIdeal
      rwa [show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) = c from RingOfIntegers.ext (star_star (c : D.host.E))], rfl⟩
  have h2 : IsIdemAt (cA D b) (GlobalTheory.IdemSupport.cP j) :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 j _ b hb hc
  rw [← e] at h2
  have hij : i = GlobalTheory.IdemSupport.cP j := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [ha.2 x hx, h2.2 x hx]
  rw [hij]
  exact hc

open Classical in
theorem splitSet_union {P H : Finset (Pl D.host.E)} (hP : SplitSet P) (hH : ∀ p ∈ H, ∃ e, IsIdemAt e p)
    (hc : ∀ p ∈ P ∪ H, ∀ p' ∈ P ∪ H, p ∈ H ∨ p' ∈ H → ¬ Lev.IsConjPl p p') : SplitSet (P ∪ H) := by
  classical
  have hid : ∀ p ∈ P ∪ H, IsIdemAt (idemAt p) p := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact hP.isIdemAt h
    · obtain ⟨e, he⟩ := hH p h
      rw [idemAt_eq he]
      exact he
  refine ⟨idem (P ∪ H), ⟨idemAt, hid, rfl⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  by_cases hh : i ∈ H ∨ j ∈ H
  · rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hid i hi).1 (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hid j hj).1) with e | e
    · exact absurd (lev_of_eq_cA (hid i hi) (hid j hj) e) (hc j hj i hi hh.symm)
    · exact e
  · push_neg at hh
    have hi' : i ∈ P := (Finset.mem_union.1 hi).resolve_right hh.1
    have hj' : j ∈ P := (Finset.mem_union.1 hj).resolve_right hh.2
    exact hP.mul_conj hi' hj'

end GlobalTheory.ChoiceAdm

end

namespace GlobalTheory.ChoiceAdm


open Classical in
theorem adm_half_of_good_of_split_disjoint : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good →
    ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)), (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) →
      Disjoint Q (X.S0 i) → (ρ.B i j b).admitted (half (ρ.ch i) Q) := by
  intro D N X ρ hρ i j b Q hsplit hdisj
  classical
  have hG := hρ.base i j b
  have hdeQ : (ρ.B i j b).de.Q = half (ρ.ch i) (X.pD i) := by rw [hρ.delta i j b]; rfl
  have deS0 : ∀ P ∈ (ρ.B i j b).de.Q, P ∈ X.S0 i := fun P hP => by
    rw [hdeQ] at hP
    exact X.primes_subset_exceptional i (mem_half.1 hP).1
  have PgS0 : ∀ P ∈ (ρ.B i j b).G.Pg, P ∈ X.S0 i := fun P hP => by
    obtain ⟨k, hk⟩ := hρ.Pg i j b P hP
    exact Finset.mem_coe.1 (X.placesOver_subset_exceptional i k hk)
  have hH : ∀ P ∈ half (ρ.ch i) Q, P ∉ X.S0 i := fun P hP h =>
    Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 h

  have hcS0 : ∀ P ∈ half (ρ.ch i) Q, ∀ P' ∈ X.S0 i, ¬ Lev.IsConjPl P P' ∧ ¬ Lev.IsConjPl P' P := by
    intro P hP P' hP'
    refine ⟨fun hc => hH P hP ?_, fun hc => hH P hP ?_⟩
    · exact hρ.goodSetup_badPlaces_conj i P' hP' P (GlobalTheory.GalChar.isConjPl_symm (isConjPl_of_lev hc))
    · exact hρ.goodSetup_badPlaces_conj i P' hP' P (isConjPl_of_lev hc)
  have hA : ∀ P ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q, P ∈ X.S0 i := fun P hP =>
    (Finset.mem_union.1 hP).elim (PgS0 P) (deS0 P)
  refine ⟨⟨⟨(ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q ∪ half (ρ.ch i) Q, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_left
  · exact Finset.union_subset (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right
  · refine splitSet_union ?_ (fun p hp => exists_idem (hsplit p (mem_half.1 hp).1)) ?_
    · obtain ⟨P0, h1, h2, h3⟩ := hG.places.split
      exact h3.mono (Finset.union_subset h1 h2)
    · intro p hp p' hp' hh hc
      by_cases h1 : p ∈ half (ρ.ch i) Q
      · by_cases h2 : p' ∈ half (ρ.ch i) Q
        · by_cases e : p = p'
          · subst e
            exact not_lev_self (hsplit p (mem_half.1 h1).1) hc
          · exact ((hρ.ch i).pair p p' (isConjPl_of_lev hc) e).1 (mem_half.1 h1).2 (mem_half.1 h2).2
        · have : p' ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q := (Finset.mem_union.1 hp').resolve_right h2
          exact (hcS0 p h1 p' (hA p' this)).1 hc
      · have hpA : p ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q := (Finset.mem_union.1 hp).resolve_right h1
        have h2 : p' ∈ half (ρ.ch i) Q := hh.resolve_left h1
        exact (hcS0 p' h2 p (hA p hpA)).2 hc
  · refine Finset.disjoint_union_right.2 ⟨hG.places.disj, Finset.disjoint_left.2 fun p hp hq => hH p hq (PgS0 p hp)⟩
  · intro PP hPP PP' hPP'
    rcases hPP with h | h
    · exact hG.places.prime PP (Or.inl h) PP' hPP'
    · rcases Finset.mem_union.1 h with h | h
      · exact hG.places.prime PP (Or.inr h) PP' hPP'
      · refine hρ.goodSetup_count_eq_zero_off_badPlaces i PP' fun hS => ?_
        rcases hPP' with e | hc
        · exact hH PP h (e ▸ hS)
        · exact (hcS0 PP h PP' hS).1 hc
  · exact Finset.disjoint_left.2 fun p hp hq => hH p hq (deS0 p hp)

end GlobalTheory.ChoiceAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries

open MvPolynomial Matrix

theorem eq_zero_of_coefFn_id_eq_zero (D : D7) (n : ℕ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n)
    (hF : ∀ x : GLR D n, coefFn (RingHom.id ℂ) lam F x = 0) : F = 0 := by
  classical
  set d : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ :=
    ∏ τ, (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)).det with hd
  have hev : ∀ v : D.what₂.Tau × Fin n × Fin n → ℂ, eval v d = ∏ τ, (Matrix.of fun a b => v (τ, a, b)).det := by
    intro v
    rw [hd, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, eval_X]
  have hd0 : d ≠ 0 := by
    intro h
    have := hev (fun w => (1 : Matrix (Fin n) (Fin n) ℂ) w.2.1 w.2.2)
    rw [h, map_zero] at this
    have h1 : ∀ τ : D.what₂.Tau, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det = 1 := by
      intro τ
      have : (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b) = 1 := by ext a b; rfl
      rw [this, det_one]
    rw [Finset.prod_eq_one fun τ _ => h1 τ] at this
    exact zero_ne_one this
  have hFd : F * d = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul, map_zero, hev]
    by_cases h : ∏ τ, (Matrix.of fun a b => v (τ, a, b)).det = 0
    · rw [h, mul_zero]
    · have hτ : ∀ τ, (Matrix.of fun a b => v (τ, a, b)).det ≠ 0 := fun τ hτ =>
        h (Finset.prod_eq_zero (Finset.mem_univ τ) hτ)
      let x : GLR D n := fun τ => GeneralLinearGroup.mkOfDetNeZero _ (hτ τ)
      have hx := hF x
      rw [coefFn] at hx
      have hu : ((detFam (fun τ => (lam τ).detShift) x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := (mul_eq_zero.mp hx).resolve_left hu
      have h3 : (fun w : D.what₂.Tau × Fin n × Fin n => (x w.1).val w.2.1 w.2.2) = v := by
        funext w
        rfl
      rw [h3] at h2
      have h4 : eval v F = 0 := by
        rw [← h2]
        rfl
      rw [h4, zero_mul]
  exact (mul_eq_zero.mp hFd).resolve_right hd0

end GlobalTheory.ExportSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexCoefficientMapCoreFieldProperties
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AdTh.CoefC

open MvPolynomial

section General

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n)

def upL : VV K lam →ₛₗ[φ] VV K' lam where
  toFun := CoefExt.up φ lam
  map_add' x y := Subtype.ext (by simp [CoefExt.up, map_add (f := _)])
  map_smul' a x := Subtype.ext (by simp [CoefExt.up, smul_eq_C_mul, map_mul, map_C])

theorem upL_apply (v : VV K lam) : upL φ lam v = CoefExt.up φ lam v := rfl

theorem up_id (v : VV K lam) : CoefExt.up (RingHom.id K) lam v = v :=
  Subtype.ext (by simp [CoefExt.up, MvPolynomial.map_id])

theorem up_comp {K'' : Type} [Field K''] (ψ : K' →+* K'') (v : VV K lam) :
    CoefExt.up ψ lam (CoefExt.up φ lam v) = CoefExt.up (ψ.comp φ) lam v :=
  Subtype.ext (by simp [CoefExt.up, MvPolynomial.map_map])

theorem up_bVV_linearIndependent : LinearIndependent K' fun j => CoefExt.up φ lam (bVV K lam j) := by
  classical
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · intro v _
    obtain ⟨a, rfl⟩ := CoefExt.exists_coord φ lam v
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Module.finrank_eq_card_basis (bVV K' lam)]

theorem up_linearIndependent (ψ : K →+* ℂ) {m : ℕ} (b : Fin m → VV K lam) (hb : LinearIndependent K b) :
    LinearIndependent ℂ fun j => CoefExt.up ψ lam (b j) :=
  CoefExt.linearIndependent (φ := RingHom.id K) (c₀ := upL ψ lam) (c' := upL ψ lam)
    (fun v => by rw [upL_apply, up_id]; rfl) (up_bVV_linearIndependent ψ lam) b hb

theorem injective_of_basis {W : Type} [AddCommGroup W] [Module K W] {ι : Type} [Fintype ι] (B : Module.Basis ι K (VV K lam))
    (c : VV K lam →ₗ[K] W) (h : LinearIndependent K fun j => c (B j)) : Function.Injective c := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hs : ∑ j, B.repr x j • c (B j) = 0 := by
    rw [← hx]
    conv_rhs => rw [← B.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have h0 := Fintype.linearIndependent_iff.1 h _ hs
  rw [← B.sum_repr x]
  simp [h0]

end General

end GlobalTheory.AdTh.CoefC


open GlobalTheory.AdTh.CoefC in
set_option maxHeartbeats 800000 in
theorem GlobalTheory.AdTh.CoefC.coefMap_complex_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ (hw : VsV D i T.Q.c.F), hwOK T.Q.c (lamV D i) hw → ‖c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) hw)‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (rhoM T.Q.c (fun τ => embF T.Q.c (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v)) = (R.cV i).ρ γ (c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v))) ∧ Submodule.span ℂ (Set.range fun v => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v)) = ⊤ ∧ (∀ (m : ℕ) (b : Fin m → VsV D i T.Q.c.F), LinearIndependent T.Q.c.F b → LinearIndependent ℂ (fun j => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (b j)))) ∧ Function.Injective c0 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hT i hstd c0 hc hw hwo
  obtain ⟨gramR, c0R, c0L, hT', hC⟩ := hc
  have hE : ∀ v : VsV D i D.what₂.LL, c0 (CoefExt.up D.what₂.embLL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw', h⟩ := hC v
    rw [show CoefExt.up D.what₂.embLL (lamV D i) v = w from Subtype.ext hw'.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT'.mapL i

  have hli : ∀ (m : ℕ) (b : Fin m → VsV D i ℂ), LinearIndependent ℂ b → LinearIndependent ℂ fun j => c0 (b j) :=
    fun m b hb => CoefExt.linearIndependent (W := (R.cV i).W) (c' := c0) hE h2 b hb
  have hinj : Function.Injective c0 := by
    classical
    let B := (bVV ℂ (lamV D i)).reindex (Fintype.equivFin _)
    refine injective_of_basis (lamV D i) B c0 ?_
    exact hli _ _ B.linearIndependent
  refine ⟨?_, ?_, ?_, fun m b hb => hli m _ (up_linearIndependent _ _ b hb), hinj⟩
  ·
    have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hstd
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hstd.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : CoefExt.up (inC T.Q.c) (lamV D i) hw = CoefExt.up D.what₂.embLL (lamV D i) v := by
      apply Subtype.ext
      show MvPolynomial.map (inC T.Q.c) (hw : Pol T.Q.c.F D.what₂.Tau (Vc D i).rank) =
        MvPolynomial.map D.what₂.embLL (Formalism.L2.DIV.ten _)
      have hw' := hwo
      unfold hwOK at hw'
      rw [hw', GlobalTheory.Proof.TensorMapDescent.map_ten, GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      rw [Formalism.L2.DIV.map_extremal, Formalism.L2.DIV.map_extremal]
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := inner_of_coefTie (hT'.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  ·
    intro γ γE hγ v
    let alg := algebraMap T.Q.c.F D.what₂.LL
    have hres : D.what₂.embLL.comp alg = inC T.Q.c := res_embLL T hT.alg hT.laws.pins.2.2.1
    have hup : ∀ w : VsV D i T.Q.c.F, c0 (CoefExt.up (inC T.Q.c) (lamV D i) w) = c0L i (CoefExt.up alg (lamV D i) w) := by
      intro w
      rw [← hE, up_comp, hres]
    have hlab : (fun τ => alg.comp (embF T.Q.c (tauE D τ))) = labLL D := by
      funext τ
      apply RingHom.ext
      intro x
      apply D.what₂.embLL.injective
      have e1 := RingHom.congr_fun (embV_spec (σ' := RingHom.id ℂ) D.what₂.embLL (by rfl) τ) x
      have e2 := RingHom.congr_fun hres (embF T.Q.c (tauE D τ) x)
      exact e2.trans e1.symm
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    rw [hup, hup, rhoM, dite_eq_left hu, hγE, CoefExt.up_rhoVr, hlab]
    exact h1 γ γE hγ _
  ·
    have hs := CoefExt.span_top (W := (R.cV i).W) (c' := c0) hE h3
    refine top_le_iff.1 (hs ▸ Submodule.span_le.2 ?_)
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, rfl⟩ := CoefExt.exists_coord (inC T.Q.c) (lamV D i) w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Submodule.sum_mem _ fun j _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexPrincipalLevelEqRealisationPrincipalLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.LevKProof

variable {D : D7}

theorem blkOf_zero_of_le {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem secondBlockIndex_eq_zero_of_dim_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_singleBlock_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [secondBlockIndex_eq_zero_of_dim_le h] at hik
  exact absurd hik (lt_irrefl _)

end GlobalTheory.SeriesTie.LevKProof

namespace GlobalTheory.SeriesTie


open LevKProof in
theorem levK_eq_levG_triv : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw}, RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hp i j b
  unfold Setup.levK levG
  rw [hp.frT]
  congr 1
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (flag1L (ρ.B i j b).G.levT) =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    unfold parLev
    have hP : (flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hp.Pg i j b
    have hb : (blkOf (flag1L (ρ.B i j b).G.levT).r (flag1L (ρ.B i j b).G.levT).t : Fin (Wc D j).rank → ℕ) =
        blkOf (Rl.datWp j Rl.triv).r (Rl.datWp j Rl.triv).t :=
      (blkOf_zero_of_le le_rfl).trans (blkOf_zero_of_le hr).symm
    have hb2 : (blk2 (flag1L (ρ.B i j b).G.levT).r : Fin (Wc D j).rank → ℕ) = blk2 (Rl.datWp j Rl.triv).r :=
      (secondBlockIndex_eq_zero_of_dim_le le_rfl).trans (secondBlockIndex_eq_zero_of_dim_le hr).symm
    rw [hP, hb, hb2]
    rfl
  have h1 : (flag1L (ρ.B i j b).G.levT).P.H = ⊥ := rfl
  have h2 : (Rl.datWp j Rl.triv).P.H = ⊥ := rfl

  have key : ∀ (x : GL (Fin (Wc D j).rank) (Lev.EAf D)) (PP : Pl D.host.E) (e1 : PP ∈ (flag1L (ρ.B i j b).G.levT).Pg)
      (e2 : PP ∈ (Rl.datWp j Rl.triv).Pg) (a c : Fin (Wc D j).rank),
      (rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x ⟨PP, e1⟩).val a c =
        (rTup (Rl.βW j) (Rl.datWp j Rl.triv) x ⟨PP, e2⟩).val
          (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) := by
    intro x PP e1 e2 a c
    unfold rTup
    erw [upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le le_rfl _)]
    rfl
  have hiff : ∀ x : GL (Fin (Wc D j).rank) (Lev.EAf D),
      rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x = 1 ↔ rTup (Rl.βW j) (Rl.datWp j Rl.triv) x = 1 := by
    intro x
    constructor
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e1 : PP.1 ∈ (flag1L (ρ.B i j b).G.levT).Pg := by
        show PP.1 ∈ (ρ.B i j b).G.Pg
        rw [hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 e1 PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
      rw [h] at hk
      refine hk.symm.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      erw [Matrix.one_apply]
      simp [Fin.ext_iff]
      rfl
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e2 : PP.1 ∈ (Rl.datWp j Rl.triv).Pg := by
        show PP.1 ∈ Rl.Pg
        rw [← hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 PP.2 e2 a c
      rw [h] at hk
      refine hk.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      rfl
  ext x
  change (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _) ↔ (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _)
  rw [hpar, h1, h2, Subgroup.mem_bot, Subgroup.mem_bot, hiff]

end GlobalTheory.SeriesTie
end

