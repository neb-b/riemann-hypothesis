module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayField
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DatEqOfPhiHat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0772

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRes

section General

variable {D : D7}

theorem locK_conj {c c' : (AE D)ˣ →* Circle} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ')
    (τ : ℂ ≃+* ℂ) (hc : ∀ x, ((c' x : Circle) : ℂ) = τ ((c x : Circle) : ℂ)) (P : Pl D.host.E) (k : D.host.Eˣ) :
    ((χ'.locK P k : ℂˣ) : ℂ) = τ ((χ.locK P k : ℂˣ) : ℂ) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  rw [← h.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), ← h'.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), hc]

theorem exists_lift (P : Pl D.host.E) (u : (kP P)ˣ) :
    ∃ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a ∧ (u : kP P) = Ideal.Quotient.mk _ a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have h0 : (a : D.host.E) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    rw [this, map_zero] at ha
    exact u.ne_zero ha.symm
  exact ⟨a, Units.mk0 _ h0, rfl, ha.symm⟩

theorem unrAt_of_isRes_one {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} (h : IsRes χ P 1) : χ.UnrAt P := by
  have key : ∀ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a → a ∉ P.asIdeal → χ.locK P k = 1 := by
    intro a k hk ha
    have := P.isMaximal
    have hu : IsUnit (Ideal.Quotient.mk P.asIdeal a) := by
      let _ := Ideal.Quotient.field P.asIdeal
      exact (Ne.isUnit (fun h0 => ha (Ideal.Quotient.eq_zero_iff_mem.1 h0)))
    exact (h a k hu.unit hk rfl).symm
  refine GlobalTheory.EtaConjType.unrAt_of_locK χ P fun u hu => ?_
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer (u : D.host.E) hu.le
  have hd' : d ∉ P.asIdeal := hd
  have hd0 : (d : D.host.E) ≠ 0 := by
    intro h0
    have : d = 0 := by exact_mod_cast h0
    exact hd' (this ▸ P.asIdeal.zero_mem)
  have hn : n ∉ P.asIdeal := by
    rw [← P.valuation_eq_one_iff_notMem (K := D.host.E), ← hnd, map_mul, hu, one_mul]
    exact (P.valuation_eq_one_iff_notMem (K := D.host.E)).2 hd'
  have e1 := key d (Units.mk0 _ hd0) rfl hd'
  have e2 := key n (u * Units.mk0 _ hd0) hnd hn
  rwa [map_mul, e1, mul_one] at e2

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (τ : ℂ ≃+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (hχ : ∀ PP ∈ Pg, ∀ x, τ ((χ PP x : ℂˣ) : ℂ) = ((χ PP x : ℂˣ) : ℂ))
    (hξ : ∀ PP ∈ Q, ∀ x, ((ξ' PP x : ℂˣ) : ℂ) = τ ((ξ PP x : ℂˣ) : ℂ)) (x) :
    ((levFn β ⟨r, hr, t, 1, Pg, Q', LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ'⟩ x : ℂˣ) : ℂ) =
      τ ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp only [h1, one_mul, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hχ PP hP]
  · exact Finset.prod_congr rfl fun PP hP => hξ PP hP _

theorem lev_congr (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hr : r ≤ V.rank) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (levEnv V β ⟨r, hr, t, 1, Pg, Q', P, χ, ξ'⟩).J = (levEnv V β ⟨r, hr, t, 1, Pg, Q, P, χ, ξ⟩).J := by
  subst hQ
  rfl

theorem levEnv_chi (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : Bridge.Gf V)
    (hk : k ∈ (levEnv V β L).J) :
    (levEnv V β L).χ ⟨k, hk⟩ = levFn β (Lev.flag1L L) (Formalism.UG.bc (Lev.swapAE D) k.1) := rfl

theorem principalLevel_definite_datum_flag_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    Lev.flag1L (L.datVt i t) = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, LevelP.triv L.Pg D.R.r ℂ,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem datVt_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    L.datVt i t = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, (LevelP.triv L.Pg D.R.r ℂ).conj,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem lev_datVt {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) {t t' : T0} (h : L.Q t' = L.Q t) :
    (levEnv (Vc D i) (L.βV i) (L.datVt i t')).J = (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J := by
  rw [datVt_eq, datVt_eq]
  exact lev_congr (Vc D i) (L.βV i) (r_le_V i) D.R.t L.Pg h _ _ (L.xiR t) (L.xiR t')

end General


set_option maxHeartbeats 1000000 in
theorem conj_res : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), ConjTup R τ t t' → (∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ)) ∧ (∀ PP ∈ R.Q t, R.xiR t PP ≠ 1) ∧ (∀ P, (((R.xiH t').val P : ℂˣ) : ℂ) = τ (((R.xiH t).val P : ℂˣ) : ℂ)) ∧ ∀ i : Fin D.R.m, FixBase T R i τ → levJ R i t' = levJ R i t ∧ ∀ k (hk : k ∈ levJ R i t) (hk' : k ∈ levJ R i t'), (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC τ t t' hct
  have hL := hC.lev
  have hloc := locK_conj (hL.xi t) (hL.xi t') τ hct.2
  have h1 : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ) := by
    intro PP hP x
    obtain ⟨a, k, hk, hx⟩ := exists_lift PP x
    rw [hL.xiR t PP hP a k x hk hx, hL.xiR t' PP (hct.1 ▸ hP) a k x hk hx]
    exact hloc PP k
  refine ⟨h1, fun PP hP h => ?_, fun P => hloc P _, fun i hτ => ⟨?_, fun k hk hk' => ?_⟩⟩
  · exact (hL.Q_ram t PP).2 (Or.inl hP) (unrAt_of_isRes_one (h ▸ hL.xiR t PP hP))
  · exact lev_datVt R.toLevCh i hct.1
  · rw [levEnv_chi, levEnv_chi, principalLevel_definite_datum_flag_eq, principalLevel_definite_datum_flag_eq]
    exact levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hct.1 τ (R.chi ((i : ℕ) + 1)) (R.xiR t) (R.xiR t') hτ.chi h1 _

end GlobalTheory.ConjRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CurveOverOfRayIn
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwistRat.Field

theorem curveOver_of_rayIn : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ (N : ℕ), 3 ≤ N →
    ∀ (Fc : IntermediateField ℚ ℂ) (σ : Fc →+* ℂ), RayIn D N σ.fieldRange → GlobalTheory.CompRat.CurveOver Q.H Fc N := by
  intro _ D Q hP N hN Fc σ hray
  obtain ⟨L, _, _, _, _, hL, j, -, hjv⟩ := hray

  have hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap D.host.K L) N :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray N hL.1 fun I hI hc => (hL.2.2 I hI hc).1

  let S : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange
  let e : Fc ≃ₐ[ℚ] S := AlgEquiv.ofInjectiveField σ.toRatAlgHom
  have hS : ∀ x, j x ∈ S := fun x => by
    obtain ⟨y, hy⟩ := hjv x
    exact ⟨y, hy⟩
  let j' : L →+* S := j.codRestrict S hS
  let ψ : L →+* ℂ := (algebraMap Fc ℂ).comp (((e.symm : S ≃+* Fc) : S →+* Fc).comp j')
  have hψ : ψ.toRatAlgHom.fieldRange ≤ Fc := by
    rintro _ ⟨x, rfl⟩
    exact (e.symm (j' x)).2

  have hsq : ∃ a : D.host.K, a ^ 2 = -(Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [hP.1]
    apply Subtype.ext
    have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
    simpa using hb
  obtain ⟨hW, hrt⟩ := GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField D.host.E Q.H D.host.K L
    (algebraMap D.host.K L) ψ (Formalism.L2.Pj.LPb.finrank_K D) hsq N hN hC
  refine (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn D.host.E Q.H Fc N (by omega)).1 (hψ hrt) fun Λ hΛ => ?_
  obtain ⟨h1, h2⟩ := hW Λ hΛ
  exact ⟨hψ h1, fun s hs => hψ (h2 s hs)⟩

end GlobalTheory.TwistRat.Field
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRelation

theorem relation_conj {K C X : Type} [Field K] [AddCommGroup C] [Module K C] (σ : K →+* ℂ) (Φ : C →ₛₗ[σ] (X → ℂ))
    (hΦ : ∀ (m : ℕ) (b : Fin m → C), LinearIndependent K b → LinearIndependent ℂ fun k => Φ (b k))
    (τ : ℂ ≃+* ℂ) (hτ : ∀ x, τ (σ x) = σ x) {n : ℕ} (a : Fin n → ℂ) (f : Fin n → C)
    (h : ∀ g, (0 : ℂ) = ∑ k, a k * Φ (f k) g) (g : X) : (0 : ℂ) = ∑ k, τ (a k) * Φ (f k) g := by
  let S := Submodule.span K (Set.range f)
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range f)
  let b := Module.finBasis K S
  have hb := hΦ _ (fun l => (b l : C)) (b.linearIndependent.map' S.subtype (Submodule.ker_subtype _))
  let c : Fin n → Fin (Module.finrank K S) → K := fun k l => b.repr ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩ l
  have hf : ∀ k, f k = ∑ l, c k l • (b l : C) := fun k => by
    have h1 := congrArg S.subtype (b.sum_repr ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    exact h1.symm
  have key : ∀ (a' : Fin n → ℂ) (x : X), ∑ k, a' k * Φ (f k) x = ∑ l, (∑ k, a' k * σ (c k l)) * Φ (b l) x := by
    intro a' x
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf k, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smulₛₗ, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have h0 : ∀ l, ∑ k, a k * σ (c k l) = 0 := by
    refine Fintype.linearIndependent_iff.1 hb _ ?_
    funext x
    rw [Finset.sum_apply]
    exact ((h x).trans (key a x)).symm
  rw [key]
  refine (Finset.sum_eq_zero fun l _ => ?_).symm
  have h1 := congrArg τ (h0 l)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hτ, map_zero] at h1
  rw [h1, zero_mul]

theorem exists_semilinear {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    ∃ Φ : T.R j →ₛₗ[σ] (GA D W → ℂ), (∀ f, Φ f = phiC T hV a f) ∧ ∀ f g, Φ f g =
      ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * adel W (castDict hV (T.dict j σ))
        (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ)) (rdU (T.U j σ) f) g := by
  subst hV
  exact ⟨(((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) • adel (T.V j σ) (T.dict j σ)
    (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ))).comp (rdU (T.U j σ)), fun _ => rfl, fun _ _ => rfl⟩


set_option maxHeartbeats 1000000 in
theorem expands_zero_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ τ : ℂ ≃+* ℂ, (∀ a : T.Q.c.F, τ (a : ℂ) = (a : ℂ)) → ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n), Expands M (κ i) (fun _ => 0) a f → Expands M (κ i) (fun _ => 0) (fun k => τ (a k)) f := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hfw i Tp tup M _ τ hτ n a f h
  obtain ⟨fw⟩ := hfw
  have hσ : GoodEmb T.Q.c M.s0 := T.toCore.good_σ₀
  have hex := exists_semilinear T M.hV (wtA (κ i))
  obtain ⟨Φ, h1, h2⟩ := hex
  have hI := GlobalTheory.PhiIndep.phiC_indep D T κ fw.laws i M.s0 hσ M.hV
  intro g
  have hr := relation_conj M.s0 (Φ.comp (T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype)
    (fun m b hb => (funext fun k => h1 (b k : T.R ((i : ℕ) + 1))).symm ▸ hI m b hb) τ hτ a f
    (fun x => (h x).trans (Finset.sum_congr rfl fun k _ => congrArg (a k * ·) (h2 _ x).symm)) g
  exact hr.trans (Finset.sum_congr rfl fun k _ => congrArg (τ (a k) * ·) (h2 _ g))

end GlobalTheory.ConjRelation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterEqOfMarkedLatticeIsometry
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
namespace GlobalTheory.MarkIso

open GlobalTheory.Member


set_option maxHeartbeats 2000000 in
theorem xi_det_eq_of_marked_isometry : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : LinearMap.range io = latG V 1)
    (A A' : Datum H) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La)
    (X X' : Data D.host.E V.rank) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (g g' : GA D V)
    (hW : ModelW V rfl X) (hW' : ModelW V rfl X')
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin V.rank → D.host.E) (φ b)))
    (hE' : ∀ a b, ((A'.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hL : (X.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g : Set _))
    (hL' : (X'.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g' : Set _))
    (hm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V ((φ (t a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hm' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V ((φ' (t' a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (gam : A.La ≃ₗ[𝓞 D.host.E] A'.La) (hgE : ∀ a b, A'.EF (gam a) (gam b) = A.EF a b)
    (hgm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ x, gam (t a) = t' a + l.M • x)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1), xi (Matrix.GeneralLinearGroup.det (finHom V g')) = xi (Matrix.GeneralLinearGroup.det (finHom V g)) := by
  intro D H Dw l V io hio A A' t t' X X' φ φ' g g' hW hW' hE hE' hL hL' hm hm' gam hgE hgm xi hxi1 hxi2
  have hGm : X'.Gm = X.Gm := hW'.1.trans hW.1.symm
  have hξ : X'.ξ0 = X.ξ0 := hW'.2.trans hW.2.symm
  let φL : A.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := X.Λ.subtype ∘ₗ φ.toLinearMap
  let φL' : A'.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := X'.Λ.subtype ∘ₗ φ'.toLinearMap
  have hr : Set.range φL = X.Λ := by
    ext v
    exact ⟨by rintro ⟨a, rfl⟩; exact (φ a).2, fun hv => ⟨φ.symm ⟨v, hv⟩,
      congrArg Subtype.val (φ.apply_symm_apply ⟨v, hv⟩)⟩⟩
  have hr' : Set.range φL' = X'.Λ := by
    ext v
    exact ⟨by rintro ⟨a, rfl⟩; exact (φ' a).2, fun hv => ⟨φ'.symm ⟨v, hv⟩,
      congrArg Subtype.val (φ'.apply_symm_apply ⟨v, hv⟩)⟩⟩
  have hcc : cc (-X.ξ0) = -(-X.ξ0) := by
    have := X.ξ0_im
    simp only [cc, map_neg] at this ⊢
    rw [this]
  obtain ⟨δ', hδ1, hδ2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry _ H A A' V.rank (-X.ξ0) X.Gm φL φL' gam hcc
    ⟨Subtype.val_injective.comp φ.injective, by rw [hr]; exact X.Λ_span, X.Gm_herm, X.Gm_det,
      fun x y => hE x y⟩
    ⟨Subtype.val_injective.comp φ'.injective, by rw [hr']; exact X'.Λ_span, hGm ▸ X'.Gm_herm, hGm ▸ X'.Gm_det,
      fun x y => by rw [hE' x y, hGm, hξ]; rfl⟩ hgE
  have hG0 : X.Gm = -(HSpace.gram V)ᵀ := by
    rw [hW.1]
    simp
  obtain ⟨r1, -, r3, -⟩ := _root_.GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨δ, hδ⟩ := r3 δ' (by rw [← hG0]; exact hδ1)
  have hLg : Set.range φL = latG V g := hr.trans (hL.trans (Set.image_id _))
  have hLg' : Set.range φL' = latG V g' := hr'.trans (hL'.trans (Set.image_id _))
  obtain ⟨u, h1, h2, h3⟩ := GlobalTheory.ConjMark.exists_of_matched V g g' δ δ' 1 l.M (by have := l.three_le; omega) l.Mb _
    l.prod hδ (fun v => by
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← hLg, ← hLg']
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, hδ2 a⟩
      · rintro ⟨a, ha⟩
        refine ⟨gam.symm a, ?_⟩
        have e := hδ2 (gam.symm a)
        rw [LinearEquiv.apply_symm_apply, ha] at e
        have e' := congrArg (fun t => ((δ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ t) e
        simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using e'.symm)
    (fun v hv => by rw [Matrix.one_mulVec]; exact hv)
    (fun b hb x hx => by
      rw [← hio] at hx
      obtain ⟨x, rfl⟩ := hx
      have hv : b • x ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
        Submodule.smul_mem_smul hb trivial
      rw [← map_smul]
      refine ⟨φL (t (b • x)), φL' (t' (b • x)), hm _ hv, hm' _ hv, ?_⟩
      obtain ⟨z, hz⟩ := hgm _ hv
      refine ⟨-φL' z, ?_, ?_⟩
      · rw [← SetLike.mem_coe, ← hLg']
        exact ⟨-z, map_neg _ _⟩
      · rw [Matrix.one_mulVec, ← hδ2, hz, map_add (f := _), map_nsmul, smul_neg]
        abel)
  have hδQ : δ ∈ GQ V := (r1 δ).2 ⟨δ', hδ⟩
  have h3' : (finHom V u).1.det * 1 - 1 ∈
      GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (l.Mb : Set (𝓞 D.host.E))) := by
    simpa [Algebra.TensorProduct.one_def] using h3
  have hq := GlobalTheory.DetTranslate.quot_cong_one D.host.F (cF D) l.M l.Mb _ l.coprime l.prod
    (fun b hb => ⟨H.bar b, Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hb, H.bar_eq b⟩)
    _ _ 1 (GlobalTheory.DetTranslate.det_int_of_gLat V h1) (GlobalTheory.DetTranslate.det_int_of_gLat V (GlobalTheory.DetTranslate.gLat_one V))
    (finHom_herm_det D V u).2.1 (finHom_herm_det D V 1).2.1 h3' (by simp)
  have hK := hxi1 u h1 (by
    obtain ⟨w, hw, e⟩ := hq
    refine ⟨w, hw, ?_⟩
    simpa using e)
  have h4 := congrArg (fun g => xi (Matrix.GeneralLinearGroup.det g)) h2
  simp only [map_mul] at h4
  rw [hK, hxi2 δ hδQ, mul_one, one_mul] at h4
  exact h4

end GlobalTheory.MarkIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspCoefficient
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.ThetaSumDescent

theorem exists_cusp_thetaSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → l.A = 1 → ∀ [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (dδ : DeltaDat Xo c n) (La : GenLat E n) (T : Type) [Fintype T] (cs : T → Rul dδ.Xo₂ dδ.c₂) (e : ℕ) (w : T → (Fin n → LevQ Dw dδ.l₂) → c.F) (P : T → MvPolynomial (LtN Dw n) c.F), Dom a n → LastPos Dw a → dδ.IsLev → dδ.l₂.A = 1 → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → La.Unimod → La.TrivAt dδ.l₂.M → La.LevOK N dδ.l₂.M → 0 < e → (∀ t, cs t ∈ sec dδ.Xo₂ dδ.c₂ 0 0 ∧ cs t ^ (e + 1) = cs t) → (∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → SumInv dδ cs w P → ∃ f ∈ cusp Xo c U a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) ∧ ∀ f' ∈ sec Xo c a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f' y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) → f' = f := by
  intro E _ _ _ H Dw l Xo c r U hr hU hA _ a n N d La T _ cs e w P hD hL hlev hA₂ hnab hun hT hO he hcs hP hinv
  obtain ⟨f, hf, hval⟩ := exists_sec_thetaSum d hlev hnab La N hun hT hO a cs w P (fun t => (hcs t).1) hP hinv
  refine ⟨f, ?_, hval, fun f' hf' hval' => ?_⟩
  · rw [← Formalism.L2.PjFree.cusp_ofPj]
    exact mem_cusp_of_thetaSum d (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
      (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ)) hA hlev hA₂ hnab La N hun hT hO a hD hL cs e he w P hcs hP
      f hf hval
  · refine GlobalTheory.ClassSumUnique.sec_eq_of_geometric hf' hf fun k _ _ _ y => ?_
    letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
      show algebraMap c.F k (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    obtain ⟨y₂, hy⟩ := hlev.2.2.2.2.2.2.1 k hk y
    obtain ⟨v, hv, e₁⟩ := hval k hk y y₂ hy
    obtain ⟨v', hv', e₂⟩ := hval' k hk y y₂ hy
    rw [e₁, e₂]
    unfold thLaValAt at hv hv'
    exact sum_values_eq d.nab₂ hnab La N hun hT hO a _
      (fun t => (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP t)) _ _ 1 y₂ _ _ _ _ hv hv' fun _ _ => rfl

section Shift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A]

end Shift

section Marks

open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A] [DecidableEq A]

end Marks

end GlobalTheory.ThetaSumDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNatIntegralFrameOfUniformizerMul
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FlatLift

theorem kmul_int : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (ϖ : 𝓞 D.host.E), ϖ ≠ 0 → ∃ k : ℕ, 0 < k ∧ ∀ u : WO S T, IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → IsIntM (frMapO S T βS βT (k • u)) := by
  intro D S T βS βT ϖ hϖ
  let I : Ideal (𝓞 D.host.E) := Ideal.span {ϖ}
  have hI : I ≠ ⊥ := by simpa [I, Ideal.span_singleton_eq_bot] using hϖ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem I)
  refine ⟨Ideal.absNorm I, Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)), fun u hu => ?_⟩
  have hk : ((Ideal.absNorm I : ℕ) : D.host.E) = (c : D.host.E) * (ϖ : D.host.E) := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hc
    simpa using this.symm
  have hm : (((Ideal.absNorm I) • u : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (Formalism.IndefR.Datum.toEAf D) =
      Formalism.IndefR.Datum.eToEAf D (c : D.host.E) •
        ((u.map fun w => incA D (ϖ : D.host.E) * w : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map
          (Formalism.IndefR.Datum.toEAf D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, nsmul_eq_mul]
    rw [map_natCast]
    have h1 : Formalism.IndefR.Datum.toEAf D (incA D (ϖ : D.host.E)) = Formalism.IndefR.Datum.eToEAf D (ϖ : D.host.E) := rfl
    rw [h1, ← mul_assoc, ← map_mul, ← hk, map_natCast]
  intro i j
  have he : frMapO S T βS βT ((Ideal.absNorm I) • u) =
      Formalism.IndefR.Datum.eToEAf D (c : D.host.E) • frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w) := by
    simp only [frMapO]
    rw [hm, Matrix.mul_smul, Matrix.smul_mul]
  rw [he, Matrix.smul_apply, smul_eq_mul]
  exact (Formalism.L2.Herm.intAf D.host.F D.host.E).mul_mem (Subring.subset_closure (Or.inl ⟨⟨((c : 𝓞 D.host.E) : D.host.E), ⟨c, rfl⟩⟩, rfl⟩)) (hu i j)

end GlobalTheory.FlatLift
end

