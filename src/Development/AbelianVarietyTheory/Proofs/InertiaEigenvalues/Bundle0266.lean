module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.AdmClosure

section Lat

variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
variable {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def between [IsDomain O] [IsPrincipalIdealRing O] (L₁ L₂ : Lattice (O := O) ρ) (N : Submodule O V)
    (h₁ : N ≤ L₁.T) (h₂ : L₂.T ≤ N) (hs : ∀ g, ∀ x ∈ N, ρ g x ∈ N) : Lattice (O := O) ρ where
  T := N
  stable := hs
  fg := L₁.fg.of_le h₁
  free := by
    haveI := L₁.free
    haveI : Module.Finite O L₁.T := Module.Finite.iff_fg.mpr L₁.fg
    haveI : Module.Finite O (N.comap L₁.T.subtype) := inferInstance
    haveI : Module.Free O (N.comap L₁.T.subtype) := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe h₁)
  span := by
    rw [eq_top_iff, ← L₂.span]
    exact Submodule.span_mono h₂

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def prodEquiv (A : Submodule O V) (B : Submodule O V') : ↥(A.prod B) ≃ₗ[O] (↥A × ↥B) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def prodLattice (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') : Lattice (O := O) (ρ.prod ρ') where
  T := L.T.prod L'.T
  stable := fun g x hx => ⟨L.stable g _ hx.1, L'.stable g _ hx.2⟩
  fg := L.fg.prod L'.fg
  free := by
    haveI := L.free
    haveI := L'.free
    exact Module.Free.of_equiv (prodEquiv L.T L'.T).symm
  span := by
    have h := Submodule.span_prod_eq (R := LL) (s := (L.T : Set V)) (t := (L'.T : Set V')) L.T.zero_mem L'.T.zero_mem
    rw [L.span, L'.span, Submodule.prod_top] at h
    exact h

end Lat

section Bundled

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def prodLoc (T T' : LocLat G Qp LL O) : LocLat G Qp LL O where
  V := T.V × T'.V
  ρ := T.ρ.prod T'.ρ
  cont := fun x => (T.cont x.1).prodMk (T'.cont x.2)
  L := prodLattice T.L T'.L

end Bundled

def appendEquiv {R : Type} [CommRing R] {A : Type 1} (W : A → Type) [∀ x, AddCommGroup (W x)] [∀ x, Module R (W x)]
    {ι κ : Type} (F : ι → A) (F' : κ → A) :
    ((∀ j, W (F j)) × (∀ j, W (F' j))) ≃ₗ[R] (∀ j : ι ⊕ κ, W (Sum.elim F F' j)) where
  toFun x j := match j with
    | .inl a => x.1 a
    | .inr b => x.2 b
  invFun y := (fun a => y (.inl a), fun b => y (.inr b))
  map_add' _ _ := by funext j; cases j <;> rfl
  map_smul' _ _ := by funext j; cases j <;> rfl
  left_inv _ := rfl
  right_inv _ := by funext j; cases j <;> rfl

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {t : ℕ} {Ut : ZMod n → Multiset ℤ}

theorem sumFull_prod [IsTopologicalRing LL] {μ μ' : ℕ} {T T' : LocLat G Qp LL O} (h : SumFull PD emb Γ t Ut μ T)
    (h' : SumFull PD emb Γ t Ut μ' T') : SumFull PD emb Γ t Ut (μ + μ') (prodLoc T T') := by
  obtain ⟨F, hF, e, he⟩ := h
  obtain ⟨F', hF', e', he'⟩ := h'
  let s : Fin (μ + μ') ≃ Fin μ ⊕ Fin μ' := finSumFinEquiv.symm
  have key : ∀ (g : G) (x : T.V × T'.V) (j : Fin μ ⊕ Fin μ'),
      appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e (T.ρ g x.1), e' (T'.ρ g x.2)) j =
        (Sum.elim F F' j).ρ g (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e x.1, e' x.2) j) := by
    intro g x j
    cases j with
    | inl a => exact he g x.1 a
    | inr b => exact he' g x.2 b
  refine ⟨fun j => Sum.elim F F' (s j), fun j => ?_,
    ((e.prodCongr e').trans (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F')).trans
      (LinearEquiv.piCongrLeft LL (fun j => (Sum.elim F F' j).V) s).symm, fun g x j => key g x (s j)⟩
  beta_reduce
  cases s j with
  | inl a => exact hF a
  | inr b => exact hF' b

variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    {π : Representation O G M} {π' : Representation O G M'}

theorem admissible_prod [IsTopologicalRing LL] (h : Admissible PD emb Γ t Ut π) (h' : Admissible PD emb Γ t Ut π') :
    Admissible PD emb Γ t Ut (π.prod π') := by
  obtain ⟨hf, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  obtain ⟨hf', μ', T', hT', L₂', p', hle', hp', hg', hk'⟩ := h'
  refine ⟨inferInstance, μ + μ', prodLoc T T', sumFull_prod hT hT', prodLattice L₂ L₂',
    (p.prodMap p') ∘ₗ (prodEquiv T.L.T T'.L.T).toLinearMap, Submodule.prod_mono hle hle',
    (hp.prodMap hp').comp (prodEquiv T.L.T T'.L.T).surjective, fun g x => ?_, fun x => ?_⟩
  · exact Prod.ext (hg g (prodEquiv T.L.T T'.L.T x).1) (hg' g (prodEquiv T.L.T T'.L.T x).2)
  · exact Prod.ext_iff.trans (and_congr (hk (prodEquiv T.L.T T'.L.T x).1) (hk' (prodEquiv T.L.T T'.L.T x).2))

variable [IsDomain O] [IsPrincipalIdealRing O]

theorem admissible_of_surjective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hs : Function.Surjective f) (h : Admissible PD emb Γ t Ut π) : Admissible PD emb Γ t Ut π' := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := (LinearMap.ker (f ∘ₗ p)).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ f (p x) = 0 := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  refine ⟨Finite.of_surjective f hs, μ, T, hT, between T.L L₂ N h₁ (fun x hx => ?_) (fun g x hx => ?_),
    f ∘ₗ p, h₁, hs.comp hp, fun g x => ?_, fun x => (hN x).symm⟩
  · refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx, map_zero]
  · refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    rw [hg, hf, (hN ⟨x, h₁ hx⟩).mp hx, map_zero]
  · simp only [LinearMap.comp_apply, hg, hf]

theorem admissible_of_injective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hi : Function.Injective f) (h : Admissible PD emb Γ t Ut π') : Admissible PD emb Γ t Ut π := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := ((LinearMap.range f).comap p).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ p x ∈ LinearMap.range f := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  have h₂ : L₂.T ≤ N := fun x hx => by
    refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx]
    exact zero_mem _
  have hs : ∀ g, ∀ x ∈ N, T.ρ g x ∈ N := fun g x hx => by
    refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    obtain ⟨y, hy⟩ := (hN ⟨x, h₁ hx⟩).mp hx
    exact ⟨π g y, by rw [hg, hf, hy]⟩
  let q : N →ₗ[O] M := (LinearEquiv.ofInjective f hi).symm.toLinearMap ∘ₗ
    (p ∘ₗ Submodule.inclusion h₁).codRestrict (LinearMap.range f) (fun x => (hN ⟨x, h₁ x.2⟩).mp x.2)
  have hq : ∀ x : N, f (q x) = p ⟨x, h₁ x.2⟩ := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective f hi).apply_symm_apply ⟨_, (hN ⟨x, h₁ x.2⟩).mp x.2⟩)
  refine ⟨Finite.of_injective f hi, μ, withLat T (between T.L L₂ N h₁ h₂ hs), hT.withLat _, L₂, q, h₂,
    fun y => ?_, fun g x => hi ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := hp (f y)
    exact ⟨⟨x.1, (hN x).mpr ⟨y, hx.symm⟩⟩, hi ((hq _).trans hx)⟩
  · exact (hq _).trans ((hg g ⟨x.1, h₁ x.2⟩).trans ((congrArg (π' g) (hq x).symm).trans (hf g _).symm))
  · refine Iff.trans ?_ (hk ⟨x.1, h₁ x.2⟩)
    rw [← hq x, ← map_zero f]
    exact hi.eq_iff.symm

end Per

theorem admissible_closed : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Closed := by
  intro l _ P S M M' _ _ _ _ π π'
  obtain ⟨⟨hD, hDV, -⟩, -, -, hT, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  exact ⟨fun f hf => ⟨admissible_of_injective f hf, admissible_of_surjective f hf⟩, admissible_prod⟩

end GlobalTheory.AdmClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfCocycleSolutionTeichmullerEpsilonRootPow
section
noncomputable section

namespace GlobalTheory.ExpImage.EpsSolve

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem εroot_pow_eq (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply',
      frobeniusEquiv_symm_pow_p]
    exact ih

theorem epsT_pow (s : ℕ) : epsT AI s ^ (l ^ s) = 1 + AI.μ := by
  rw [epsT, ← map_pow, εroot_pow_eq, LocAinf.μ]
  ring

theorem epsT_zero : epsT AI 0 = 1 + AI.μ := by simpa using epsT_pow AI 0

theorem μ_not_unit : ¬ IsUnit AI.μ := by
  obtain ⟨θ, -, -, -, h, -⟩ := GlobalTheory.Cyc.exists_isTheta l P AI
  intro hu
  have h0 : θ AI.μ = 0 := (h _).mpr ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := hu.map θ
  rw [h0] at this
  exact not_isUnit_zero this

theorem actW_epsT (g : GQ l) (u : ℕ) (hu : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) (j : ℕ) :
    AI.actW g (epsT AI j) = epsT AI j ^ u := by
  rw [epsT, LocAinf.actW, WittVector.map_teichmuller, ← map_pow,
    ← GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g u hu j]
  rfl

theorem actW_μ (g : GQ l) (u : ℕ) (hu : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) :
    AI.actW g AI.μ = (1 + AI.μ) ^ u - 1 := by
  have h := actW_epsT AI g u hu 0
  rw [epsT_zero, map_add (f := _), map_one] at h
  linear_combination h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ),
    Lev l s → ∀ g : GQ l, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ U : ℤ_[l],
    (l : ℤ_[l]) ^ s ∣ U - 1 → ∀ m : ℕ, ¬ l ∣ m → Solv AI K s g U (epsT AI s ^ m) := by
  intro l _ P AI K s hs g hg U hU m hm
  have hc := (GlobalTheory.Per.AinfComplete.main l AI.μ (μ_not_unit AI)).2
  obtain ⟨⟨ev, hev⟩, huniq⟩ := GlobalTheory.PowerSeriesAdicEval.exists_eval_and_unique ℤ_[l] (Ainf l) AI.μ hc
  obtain ⟨v, hv⟩ : (PowerSeries.X : PowerSeries ℤ_[l]) ∣ (1 + PowerSeries.X) ^ (1 + l ^ s) - 1 := by
    have := sub_dvd_pow_sub_pow (1 + PowerSeries.X : PowerSeries ℤ_[l]) 1 (1 + l ^ s)
    simpa using this
  have hsub : PowerSeries.HasSubst (PowerSeries.X * v : PowerSeries ℤ_[l]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  let γ : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] PowerSeries ℤ_[l] := PowerSeries.substAlgHom hsub
  have hγ : γ PowerSeries.X = PowerSeries.X * v := PowerSeries.substAlgHom_X hsub
  have hgμ : AI.actW g AI.μ = AI.μ * ev v := by
    have := congrArg ev hv
    simp only [map_sub, map_pow, map_add (f := _), map_one, map_mul, hev] at this
    rw [actW_μ AI g _ hg, this]
  have hgev : ∀ f, AI.actW g (ev f) = ev (γ f) := by
    have := huniq (((AI.actWHom g : Ainf l ≃ₐ[ℤ_[l]] Ainf l) : Ainf l →ₐ[ℤ_[l]] Ainf l).comp ev)
      (ev.comp γ) (by
        change AI.actW g (ev PowerSeries.X) = ev (γ PowerSeries.X)
        rw [hγ, map_mul, hev, hgμ]) (by
        change AI.μ ∣ AI.actW g (ev PowerSeries.X)
        rw [hev, hgμ]
        exact dvd_mul_right _ _)
    intro f
    exact DFunLike.congr_fun this f
  have hχ : ∀ h ∈ Hinf K, (P.χQ h : ℚ_[l]) = ((1 : ℕ) : ℚ_[l]) := by
    intro h hh
    have := ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K h (Hinf_le_fix hh)).2.mp hh
    rw [this]
    simp
  have hhev : ∀ h ∈ Hinf K, ∀ f, AI.actW h (ev f) = ev f := by
    intro h hh
    have hμ : AI.actW h AI.μ = AI.μ := by
      rw [actW_μ AI h 1 (hχ h hh)]
      ring
    have := huniq (((AI.actWHom h : Ainf l ≃ₐ[ℤ_[l]] Ainf l) : Ainf l →ₐ[ℤ_[l]] Ainf l).comp ev)
      ev (by
        change AI.actW h (ev PowerSeries.X) = ev PowerSeries.X
        rw [hev, hμ]) (by
        change AI.μ ∣ AI.actW h (ev PowerSeries.X)
        rw [hev, hμ])
    intro f
    exact DFunLike.congr_fun this f
  have hgE : AI.actW g (epsT AI s) = epsT AI s * (1 + AI.μ) := by
    rw [actW_epsT AI g _ hg, pow_add, pow_one, epsT_pow]
  choose pp FF hpF using GlobalTheory.ExpImage.solve_mod_pow l s hs m hm U hU γ v hv.symm hγ
  let F : ℕ → PowerSeries ℤ_[l] := fun k => Nat.rec 1 (fun k f => FF (k + 1) f) k
  have hF : ∀ k, F (k + 1) = FF (k + 1) (F k) := fun _ => rfl
  refine ⟨fun k => epsT AI s ^ m * ev (pp (k + 1) (F k)), fun k => epsT AI s ^ m * ev (F k), ?_,
    fun k h hh => ?_, fun k => ?_⟩
  · change epsT AI s ^ m * ev 1 = _
    rw [map_one, mul_one]
  · rw [map_mul, map_pow, actW_epsT AI h 1 (hχ h hh), pow_one, hhev h hh]
  · have h1 := congrArg ev (hpF (k + 1) (F k))
    have hC : ev (PowerSeries.C U) = algebraMap ℤ_[l] (Ainf l) U := ev.commutes U
    simp only [map_sub, map_pow, map_add (f := _), map_one, map_mul, hev, hC, map_natCast] at h1
    unfold Step
    beta_reduce
    rw [hF, map_mul, map_pow, hgE, hgev, hgμ, mul_pow, mul_pow]
    linear_combination (epsT AI s ^ m * AI.μ ^ (k + 1)) * h1

end GlobalTheory.ExpImage.EpsSolve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjective
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TensorInj

theorem exists_div_of_mem_closure {A D : Type} [CommRing A] [Field D] (g : A →+* D) {y : D}
    (hy : y ∈ Subfield.closure (Set.range g)) (h0 : y ≠ 0) : ∃ a b : A, b ≠ 0 ∧ g a = y * g b := by
  obtain ⟨p, hp, q, hq, e⟩ := Subfield.mem_closure_iff.1 hy
  have hr : Subring.closure (Set.range g) = g.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  rw [hr] at hp hq
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  have hb : g b ≠ 0 := fun h => h0 (by rw [← e, h, div_zero])
  refine ⟨a, b, fun h => hb (by rw [h, map_zero]), ?_⟩
  rw [← e, div_mul_cancel₀ _ hb]

theorem indep_of_fractions (l : ℕ) [Fact l.Prime] {A B D : Type} [CommRing A] [CommRing B] [CommRing D]
    (hD : IsField D) (g : A →+* D) (ι : B →+* D) (hι : Function.Injective ι) (o : Om l →+* D)
    (hB : ∀ b : B, ∃ a a' : A, g a' ≠ 0 ∧ ι b * g a' = g a)
    (hu : ∀ c : ↥(MaximalUnramifiedExtension l), ∃ b : B, ι b = o (c : Om l))
    (hv : ∀ (a b : A) (x : Om l), b ≠ 0 → x ≠ 0 → g a = o x * g b → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k)
    (m : ℕ) (x : Fin m → Om l) (hx : LinearIndependent ↥(MaximalUnramifiedExtension l) x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) (i : Fin m) : b i = 0 := by
  letI : Field D := hD.toField
  let F : Subfield D := Subfield.closure (Set.range g)
  have hg : ∀ a, g a ∈ F := fun a => Subfield.subset_closure ⟨a, rfl⟩
  have hιF : ∀ b, ι b ∈ F := fun b => by
    obtain ⟨a, a', h0, e⟩ := hB b
    rw [eq_div_of_mul_eq h0 e]
    exact F.div_mem (hg a) (hg a')
  have hK : ∀ c : ↥(MaximalUnramifiedExtension l), o (c : Om l) ∈ F := fun c => by
    obtain ⟨b, e⟩ := hu c
    exact e ▸ hιF b
  let E : IntermediateField ℚ_[l] (Om l) :=
    (F.comap o).toIntermediateField fun q => hK (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)
  have hE : ∀ y : Om l, o y ∈ F → y ∈ MaximalUnramifiedExtension l := fun y hy => by
    have hint : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
    have hle : IntermediateField.adjoin ℚ_[l] {y} ≤ E :=
      IntermediateField.adjoin_simple_le_iff.2 hy
    refine GlobalTheory.UnramValue.le_Kur_of_norm l ⟨IntermediateField.adjoin ℚ_[l] {y},
      IntermediateField.adjoin.finiteDimensional hint⟩ (fun z hz h0 => ?_)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] y)
    obtain ⟨a, a', h1, e⟩ := exists_div_of_mem_closure g (y := o z) (hle hz) ((map_ne_zero o).2 h0)
    exact hv a a' z h1 h0 e
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := IsGalois.tower_top_of_isGalois ℚ_[l] _ _
  have := _root_.GlobalTheory.GalDisj.galois_linearDisjoint ↥(MaximalUnramifiedExtension l) (Om l) D o F
    (fun y => ⟨fun h => ⟨⟨y, hE y h⟩, rfl⟩, fun ⟨c, h⟩ => h ▸ hK c⟩) m x hx (fun i => ι (b i))
    (fun i => hιF _) hb i
  exact hι (this.trans (map_zero ι).symm)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem tensorInj (l : ℕ) [Fact l.Prime] (c : Core l) : c.TensorInj := by
  obtain ⟨-, hinj, hD, -⟩ := BdRField.bdR_isField l
  have hι : Function.Injective c.ι := (ULaws.u_laws l c).2.2.2.1
  haveI : Nontrivial (Per.BdR l) := ⟨hD.exists_pair_ne⟩
  refine indep_of_fractions l hD ((algebraMap (Per.BdRp l) (Per.BdR l)).comp c.j) c.ι hι c.oD
    (fun b => ?_) (fun x => ⟨c.u x, c.ι_u x⟩) (fun a b x hb hx e => ?_)
  · obtain ⟨r, a, e⟩ := bcris_eq_acris_localization_periodT_alt l c b
    refine ⟨a, c.t ^ r, ?_, ?_⟩
    · rw [RingHom.comp_apply, ← c.ι_j, map_pow]
      exact ((((core_t_unit_fil l c).1).pow r).map c.ι).ne_zero
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← c.ι_j, ← c.ι_j, ← map_mul, map_pow, e]
  · refine @GlobalTheory.MemLoc.GaussCore.norm_eq_zpow l _ c a b x hb hx (hinj ?_)
    rw [map_mul]
    exact e

end GlobalTheory.MemLoc.TensorInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPlusFrobeniusStableSubringInFilZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.CrisPlus

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem plus_phi {b : P.R.B} (h : Plus T b) : Plus T (P.φB b) := by
  obtain ⟨N, x, hx⟩ := h
  refine ⟨N, GlobalTheory.MemLoc.phiA l x, ?_⟩
  have e : (l : P.R.B) ^ N * P.φB b = P.φB ((l : P.R.B) ^ N * b) := by
    rw [map_mul, map_pow, map_natCast]
  rw [e, T.frob, hx]
  exact GlobalTheory.CrisMaps.φB_phiA l x

theorem plus_iterate {b : P.R.B} (h : Plus T b) (j : ℕ) : Plus T (P.φB^[j] b) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact plus_phi T ih

theorem plus_add_mul {a b : P.R.B} (ha : Plus T a) (hb : Plus T b) : Plus T (a + b) ∧ Plus T (a * b) := by
  obtain ⟨N, x, hx⟩ := ha
  obtain ⟨M, y, hy⟩ := hb
  refine ⟨⟨N + M, (l : Formalism.Per.Acris l) ^ M * x + (l : Formalism.Per.Acris l) ^ N * y, ?_⟩, ⟨N + M, x * y, ?_⟩⟩
  · have e : (l : P.R.B) ^ (N + M) * (a + b) = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * a) + (l : P.R.B) ^ N * ((l : P.R.B) ^ M * b) := by
      ring
    rw [e, map_add (f := _), map_mul T.eB ((l : P.R.B) ^ M) ((l : P.R.B) ^ N * a),
      map_mul T.eB ((l : P.R.B) ^ N) ((l : P.R.B) ^ M * b), hx, hy]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  · have e : (l : P.R.B) ^ (N + M) * (a * b) = ((l : P.R.B) ^ N * a) * ((l : P.R.B) ^ M * b) := by ring
    rw [e, map_mul, hx, hy, map_mul]

theorem plus_alg (q : ℚ_[l]) : Plus T (algebraMap ℚ_[l] P.R.B q) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖q‖ hl
  have hz : ‖(l : ℚ_[l]) ^ N * q‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow]
    have hp : (0 : ℝ) < (l : ℝ) ^ N := by positivity
    rw [zpow_neg, zpow_natCast]
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact hN.le
  let z : ℤ_[l] := ⟨(l : ℚ_[l]) ^ N * q, hz⟩
  refine ⟨N, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.zA l z), ?_⟩
  have e : (l : P.R.B) ^ N * algebraMap ℚ_[l] P.R.B q = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
    change _ = algebraMap ℚ_[l] P.R.B ((l : ℚ_[l]) ^ N * q)
    rw [map_mul, map_pow, map_natCast]
  rw [e, T.zB, GlobalTheory.RingIface.zB_eq_aB_zA l z, GlobalTheory.RingIface.aB_eq_alg l]

theorem plus_ainf (x : Formalism.Per.Ainf l) : Plus T (T.eB.symm (Formalism.Per.aB l x)) :=
  ⟨0, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) x, by rw [pow_zero, one_mul, RingEquiv.apply_symm_apply]; exact GlobalTheory.RingIface.aB_eq_alg l x⟩

theorem plus_alt : Plus T P.tB := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  exact ⟨0, C.t, by rw [pow_zero, one_mul, hC.t]; rfl⟩

theorem plus_fil {b : P.R.B} (h : Plus T b) : P.ιB b ∈ Fil P 0 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨N, x, hx⟩ := h
  obtain ⟨u, hu⟩ := (GlobalTheory.MemLoc.isUnit_l_BdRp l).exists_left_inv
  have e1 : T.eD (P.ιB ((l : P.R.B) ^ N * b)) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (C.j x) := by
    rw [hC.ι, hx, C.ι_j]
  simp only [map_mul, map_pow, map_natCast] at e1
  have e2 : T.eD (P.ιB b) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N * C.j x) := by
    calc T.eD (P.ιB b)
        = (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) u * (l : Formalism.Per.BdR l)) ^ N * T.eD (P.ιB b) := by
          rw [← map_natCast (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)) l, ← map_mul, hu, map_one, one_pow, one_mul]
      _ = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N) * ((l : Formalism.Per.BdR l) ^ N * T.eD (P.ιB b)) := by
          rw [map_pow]; ring
      _ = _ := by rw [e1, ← map_mul]
  show P.ιB b ∈ (P.PD (botExt l)).Fil 0
  refine (T.fil (botExt l) 0 _).2 ?_
  rw [e2]
  exact GlobalTheory.RingIface.alg_mem_FilD_zero l _

theorem plus_props : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    (∀ b, Plus T b → Plus T (P.φB b)) ∧ (∀ b, Plus T b → ∀ j, ev P j b ∈ Fil P 0) ∧
    (∀ a b, Plus T a → Plus T b → Plus T (a + b) ∧ Plus T (a * b)) ∧
    (∀ q : ℚ_[l], Plus T (algebraMap ℚ_[l] P.R.B q)) ∧
    (∀ x : Formalism.Per.Ainf l, Plus T (T.eB.symm (Formalism.Per.aB l x))) ∧ Plus T P.tB := by
  intro l _ P AI T
  exact ⟨fun b h => plus_phi T h, fun b h j => plus_fil T (plus_iterate T h j), fun a b ha hb => plus_add_mul T ha hb,
    plus_alg T, plus_ainf T, plus_alt T⟩

end GlobalTheory.PMon.CrisPlus
end

