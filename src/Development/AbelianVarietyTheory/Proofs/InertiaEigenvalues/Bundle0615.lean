module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealSideCharacterMatch
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Formalism.LocalRingCardinality.HostCls
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionConstantsGaloisComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHorizontalVectorOfBreuilKisinJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresOfFiniteIndexSubLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SubLevel

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Gen

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

def dcRel (J' : Subgroup G) : Setoid G where
  r h h' := ∃ (γ : Γ) (k : J'), h' = ι γ * h * (k : G)
  iseqv := {
    refl := fun h => ⟨1, 1, by simp⟩
    symm := fun {h h'} ⟨γ, k, e⟩ => ⟨γ⁻¹, k⁻¹, by rw [e, map_inv, Subgroup.coe_inv]; group⟩
    trans := fun {h h' h''} ⟨γ, k, e⟩ ⟨γ₂, k₂, e₂⟩ =>
      ⟨γ₂ * γ, k * k₂, by rw [e₂, e, map_mul, Subgroup.coe_mul]; group⟩ }

theorem stab_mono_mem {J J' : Subgroup G} (hJ : J' ≤ J) {y k : G} (hk : k ∈ J) {g : Γ}
    (hg : g ∈ stab ι J' (y * k)) : g ∈ stab ι J y := by
  rw [mem_stab ι] at hg ⊢
  have h1 : (y * k)⁻¹ * ι g * (y * k) ∈ J := hJ hg
  have e : y⁻¹ * ι g * y = k * ((y * k)⁻¹ * ι g * (y * k)) * k⁻¹ := by group
  rw [e]
  exact J.mul_mem (J.mul_mem hk h1) (J.inv_mem hk)

end Gen

section Main

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable (P : ClassPres ι S σ ρ J χ) (J' : Subgroup G)

def yN (c : Quotient (dcRel ι J')) : G := P.y (P.decC c.out) * (P.decK c.out : G)

theorem yN_rel (c : Quotient (dcRel ι J')) : (dcRel ι J').r (yN P J' c) c.out := by
  show ∃ (γ : Γ) (k : J'), c.out = ι γ * yN P J' c * (k : G)
  refine ⟨P.decG c.out, 1, ?_⟩
  show c.out = ι (P.decG c.out) * (P.y (P.decC c.out) * (P.decK c.out : G)) * ((1 : J') : G)
  rw [Subgroup.coe_one, mul_one, ← mul_assoc]
  exact P.dec_spec c.out

theorem mk_yN (c : Quotient (dcRel ι J')) : Quotient.mk (dcRel ι J') (yN P J' c) = c :=
  (Quotient.sound (yN_rel P J' c)).trans (Quotient.out_eq c)

theorem reps_new : IsReps ι J' (yN P J') := by
  intro h
  refine ⟨Quotient.mk (dcRel ι J') h, ?_, ?_⟩
  · exact Quotient.exact (mk_yN P J' (Quotient.mk (dcRel ι J') h))
  · rintro i ⟨γ, k, e⟩
    have hr : (dcRel ι J').r (yN P J' i) h := ⟨γ, k, e⟩
    exact (mk_yN P J' i).symm.trans (Quotient.sound hr)

theorem stabN_finite (hJ : J' ≤ J) (c : Quotient (dcRel ι J')) : Finite (stab ι J' (yN P J' c)) := by
  haveI : Finite (stab ι J (P.y (P.decC c.out))) := Finite.of_equiv _ (P.stabI (P.decC c.out)).toEquiv
  refine Finite.of_injective
    (fun g : stab ι J' (yN P J' c) =>
      (⟨(g : Γ), stab_mono_mem ι hJ (P.decK c.out).2 g.2⟩ : stab ι J (P.y (P.decC c.out)))) ?_
  intro a b hab
  have hv := congrArg Subtype.val hab
  exact Subtype.ext hv

include P in
theorem cl_finite (hfi : (J'.subgroupOf J).FiniteIndex) : Finite (Quotient (dcRel ι J')) := by
  haveI := hfi
  refine Finite.of_surjective
    (fun p : S.Cl × (J ⧸ J'.subgroupOf J) => Quotient.mk (dcRel ι J') (P.y p.1 * ((p.2.out : J) : G))) ?_
  intro c
  obtain ⟨d, γ, k, e⟩ : ∃ (d : S.Cl) (γ : Γ) (k : J), c.out = ι γ * P.y d * (k : G) :=
    ⟨_, _, _, P.dec_spec c.out⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (s := J'.subgroupOf J) k
  have hjJ' : ((j : J) : G) ∈ J' := Subgroup.mem_subgroupOf.1 j.2
  refine ⟨(d, (QuotientGroup.mk k : J ⧸ J'.subgroupOf J)), ?_⟩
  show Quotient.mk (dcRel ι J') (P.y d * (((QuotientGroup.mk k : J ⧸ J'.subgroupOf J).out : J) : G)) = c
  rw [hj]
  have hr : (dcRel ι J').r (P.y d * ((k * (j : J) : J) : G)) c.out := by
    refine ⟨γ, ⟨((j : J) : G)⁻¹, J'.inv_mem hjJ'⟩, ?_⟩
    show c.out = ι γ * (P.y d * ((k : G) * ((j : J) : G))) * ((j : J) : G)⁻¹
    rw [e]
    group
  exact (Quotient.sound hr).trans (Quotient.out_eq c)

variable (χ' : J' →* ℂˣ) (hχ' : ∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ))
  (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))

def rhoG (y : G) (g : stab ι J' y) (x : S.V) : W :=
  (χ' (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef x)

include hχ' hρ in
theorem rhoG_rg (y : G) (g : stab ι J' y) (x : S.V) : InRg P (rhoG P J' χ' y g x) := by
  obtain ⟨x', hx'⟩ := hρ (g : Γ) x
  obtain ⟨a, ha⟩ := hχ' (stabK ι g)
  refine ⟨a • x', ?_⟩
  rw [map_smulₛₗ, hx', ha]
  rfl

def rhoGE (y : G) (g : stab ι J' y) : Module.End K S.V where
  toFun x := cinv P (rhoG P J' χ' y g x)
  map_add' x x' := by
    apply coef_injective P
    rw [map_add (f := _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _),
      coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_add (f := _), smul_add]
  map_smul' b x := by
    apply coef_injective P
    rw [map_smulₛₗ, coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_smulₛₗ, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem coef_rhoGE (y : G) (g : stab ι J' y) (x : S.V) :
    P.coef (rhoGE P J' χ' hχ' hρ y g x) = rhoG P J' χ' y g x :=
  coef_cinv P (rhoG_rg P J' χ' hχ' hρ y g x)

def rhoGN (y : G) : stab ι J' y →* Module.End K S.V where
  toFun := rhoGE P J' χ' hχ' hρ y
  map_one' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [coef_rhoGE]
    simp [rhoG, stabK_one']
  map_mul' g g' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [Module.End.mul_apply, coef_rhoGE, coef_rhoGE]
    simp only [rhoG, coef_rhoGE, map_mul, stabK_mul', Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_smul,
      smul_smul, mul_comm]

end Main

end GlobalTheory.SubLevel

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.SubLevel

theorem classPres_subLevel : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (J' : Subgroup G), J' ≤ J → (J'.subgroupOf J).FiniteIndex → ∀ χ' : J' →* ℂˣ, (∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) → ∃ (Cl : Type) (fC : Fintype Cl) (π : Cl → S.Cl) (k : Cl → J) (Gam : Cl → Type) (gG : ∀ c, Group (Gam c)) (fG : ∀ c, Fintype (Gam c)) (ρ' : ∀ c, Gam c →* Module.End K S.V) (P' : Bridge.ClassPres ι ({ S with Cl := Cl, finCl := fC, Gam := Gam, grpGam := gG, finGam := fG, ρ := ρ', Nab := fun c => S.Nab (π c), Del := fun c => S.Del (π c) } : CSD K) σ ρ J' χ'), (∀ c : Cl, P'.y c = P.y (π c) * (k c : G)) ∧ P'.coef = P.coef := by
  intro G Γ _ _ ι W _ _ K _ _ _ σ S ρ J χ P J' hJ hfi χ' hχ' hρ
  haveI : Finite (Quotient (SubLevel.dcRel ι J')) := SubLevel.cl_finite P J' hfi
  letI fC : Fintype (Quotient (SubLevel.dcRel ι J')) := Fintype.ofFinite _
  haveI hfS : ∀ c, Finite (stab ι J' (SubLevel.yN P J' c)) := fun c => SubLevel.stabN_finite P J' hJ c
  letI fG : ∀ c, Fintype (stab ι J' (SubLevel.yN P J' c)) := fun c => Fintype.ofFinite _
  exact ⟨Quotient (SubLevel.dcRel ι J'), fC, fun c => P.decC c.out, fun c => P.decK c.out,
    fun c => stab ι J' (SubLevel.yN P J' c), fun c => inferInstance, fG,
    fun c => SubLevel.rhoGN P J' χ' hχ' hρ (SubLevel.yN P J' c),
    { y := SubLevel.yN P J'
      reps := SubLevel.reps_new P J'
      stabI := fun c => MulEquiv.refl _
      coef := P.coef
      coef_li := P.coef_li
      coef_span := P.coef_span
      coef_pair := P.coef_pair
      coef_act := fun c g x => SubLevel.coef_rhoGE P J' χ' hχ' hρ (SubLevel.yN P J' c) g x },
    fun c => rfl, rfl⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlaces
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Proof.ConjugatePlaces

open GlobalTheory.IndefiniteRowSideFullHecke

section Host

variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem exists_conj_int (x : 𝓞 H.E) : ∃ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) :=
  ⟨⟨H.conj (x : H.E), (x.isIntegral_coe).map (H.conj.toAlgHom.restrictScalars ℤ)⟩, rfl⟩

variable {H}

theorem isConjPl_symm {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') : IsConjPl H w' w :=
  fun x y hy => (h y x (by rw [hy, conj_conj])).symm

theorem isConjPl_unique {w w₁ w₂ : HeightOneSpectrum (𝓞 H.E)} (h₁ : IsConjPl H w w₁)
    (h₂ : IsConjPl H w w₂) : w₁ = w₂ := by
  ext y
  obtain ⟨x, hx⟩ := exists_conj_int H y
  have hy : (y : H.E) = H.conj (x : H.E) := by rw [hx, conj_conj]
  exact (h₁ x y hy).symm.trans (h₂ x y hy)

variable (H)

end Host

section Loc

variable (D : D7) (i : D.nd.Loc)

section Pl

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Pl

end Loc

end GlobalTheory.Proof.ConjugatePlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlaces
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.NygaardFrobeniusPower

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem isUnit_φA_pow (k : ℕ) (a : LetA O n) (ha : IsUnit (algebraMap (LetA O n) W.EE a)) :
    IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) a)) := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply]
    have : algebraMap (LetA O n) W.EE (W.φA ((W.φA ^ k) a)) =
        W.φE (algebraMap (LetA O n) W.EE ((W.φA ^ k) a)) := (W.φE_ext _).symm
    rw [this]
    exact ih.map W.φE

theorem isUnit_X : IsUnit (algebraMap (LetA O n) W.EE W.X) :=
  isUnit_φA_pow W (W.s - 1) letπ W.EE_π

theorem Q_pow_φ_mem [NeZero n] (T : LocLat G Qp LL O) (M : ZMod n → ℕ)
    (hM : ∀ i, ∀ x ∈ W.Nl T (i - 1), W.Q ^ (M i) • W.φD T x ∈ W.N T)
    (x : W.DD T) (hx : x ∈ W.N T) : W.Q ^ (mx M) • W.φD T x ∈ W.N T := by
  have hx' : x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE, one_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hle : M (i + 1) ≤ mx M := le_ciSup (Set.finite_range M).bddAbove (i + 1)
  have hmem : (letE i : LetA O n) • x ∈ W.Nl T (i + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨x, hx, by simp⟩
  have h1 := hM (i + 1) _ hmem
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ h1

theorem core [NeZero n] (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (M : ZMod n → ℕ)
    (hex : ∀ y, W.map π y = 0 → ∃ z, W.map ι z = y)
    (hsat : ∀ z : W.DD T, W.map ι z ∈ W.N Tp → z ∈ W.N T)
    (hφ : ∀ i, ∀ x ∈ W.Nl Tp (i - 1), W.Q ^ (M i) • W.φD Tp x ∈ W.N Tp)
    (hγ : ∀ x ∈ W.N Tp, W.γ Tp x - x ∈ (aN W) Tp W.X)
    (e : W.DD W.one) (he : W.φD W.one e = e) (hge : ∀ g, W.γD W.one g e = e)
    (x : W.DD Tp) (hx : x ∈ W.N Tp) (c : O) (hc : W.map π x = c • e) :
    (∃ y ∈ (invN W) T (W.Q ^ mx M), W.map ι y = W.φD Tp x - x) ∧
      (∃ z ∈ (aN W) T W.X, W.map ι z = W.γ Tp x - x) := by
  constructor
  · have h0 : W.map π (W.φD Tp x - x) = 0 := by
      rw [map_sub, W.map_φ, hc, (W.φD W.one).map_smul, he, sub_self]
    obtain ⟨y, hy⟩ := hex _ h0
    refine ⟨y, hsat _ ?_, hy⟩
    change W.map ι (W.Q ^ mx M • y) ∈ W.N Tp
    rw [map_smulA, hy, smul_sub]
    exact Submodule.sub_mem _ (Q_pow_φ_mem W Tp M hφ x hx) (Submodule.smul_mem _ _ hx)
  · obtain ⟨w, hw, hw'⟩ := hγ x hx
    change W.X • w = W.γ Tp x - x at hw'
    have hX0 : W.X • W.map π w = 0 := by
      rw [← map_smulA, hw', map_sub, LocWach.γ, W.map_γ, hc, (W.γD W.one W.gam).map_smul, hge,
        sub_self]
    have h0 : W.map π w = 0 := by
      obtain ⟨u, hu⟩ := isUnit_X W
      rw [← algebraMap_smul W.EE W.X, ← hu] at hX0
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hX0
      simpa [smul_smul] using this
    obtain ⟨z, hz⟩ := hex _ h0
    have hzN : z ∈ W.N T := hsat z (hz ▸ hw)
    refine ⟨W.X • z, ⟨z, hzN, rfl⟩, ?_⟩
    rw [map_smulA, hz]
    exact hw'

end Generic


set_option maxHeartbeats 1000000 in
theorem crystalline_extension_integral_cocycle_all_places : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P8 D HW F := by
  intro D HW F Cm l _ K s LL h T M hh hT hjT Tp ι π hses hTp e heN hφe hγe x hx c hc
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hexact : Function.Exact (((HW l).W K s LL h).map ι) (((HW l).W K s LL h).map π) := by
    let E := ((F l).E K s LL h).tie
    haveI := GlobalTheory.EtaleExact.finite_OL LL
    haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
    have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
    exact (GlobalTheory.EtaleExact.exact_of_tie E
      (GlobalTheory.EtaleExact.map_ne_top_of_tie E (by
        rw [hp]
        exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL) (by
        rw [hp]
        exact GlobalTheory.EtaleExact.sep_RW LL)) T Tp ((HW l).W K s LL h).one ι π hses).2.1
  have hsat := GlobalTheory.T.mem_wachN_of_map_mem_saturated D HW F l K s LL h T Tp ((HW l).W K s LL h).one ι π hT hTp
    (GlobalTheory.NL.one_crys (HW l) h) hses
  have hjs := GlobalTheory.NL.JumpsSES.jumps_ses_and_one D HW l K s LL h T Tp ((HW l).W K s LL h).one ι π hTp hses
  have hjTp : JumpsLet ((HW l).W K s LL h) Tp M hh := by
    intro τ i hτ a ha
    rcases (hjs.1 τ a).1 ha with h1 | h1
    · exact hjT τ i hτ a h1
    · rw [hjs.2 τ a h1]
      exact ⟨by simp, by simp⟩
  have h5 := (_root_.GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm l K s LL h Tp M hh hTp hjTp).1
  have h2 := (GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm l K s LL h Tp hTp).2.2
  exact core _ T Tp ι π M (fun y hy => (hexact y).1 hy) hsat h5 h2 e hφe hγe x hx c hc

end GlobalTheory.NL.NygaardFrobeniusPower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisLimitLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_basis_limit_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val), ∃ (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), ∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r := by
  first | (exact @GlobalTheory.BKLim.limit_pre_exists) | (exact GlobalTheory.BKLim.limit_pre_exists) | (intros; apply GlobalTheory.BKLim.limit_pre_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedVectorFiltrationJumpBreuilKisin
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  intro hF l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN i hi
  have Td : LocTied l Pl AI := hStd.some
  obtain ⟨X, hX⟩ := _root_.GlobalTheory.BKGal.CrisTensDR.main l Pl AI Td LL T
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.BKGal.JumpDR.exists_odAction l Pl AI Td LL T
  obtain ⟨n, d, c, hd, h1, h2⟩ := _root_.GlobalTheory.BKGal.JumpDR.Horiz.main l a e LL hl ι P hEN i hi
  let m : Fin n → P.MMl := fun k => ⟨P.xi (d k), hd k⟩
  have key := fun j => GlobalTheory.T.mem_completionFiltration_iff_deRhamFiltration hF l a e ϖ LL hl ι P T I jB Pl AI Td hCmp X hX A hA n
    (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) m j
  refine ⟨∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)))
    (X (jB (toBcris (thetaW a LL) ϖ P (m k)))), ?_, (key i).1 h1, fun h => h2 ((key (i + 1)).2 h)⟩
  intro g hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 := _root_.GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift l Pl AI Td LL T A hA a e ϖ (c k) g hg (X (jB (toBcris (thetaW a LL) ϖ P (m k))))
  have e2 := GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant l Pl AI Td LL T X hX g (jB (toBcris (thetaW a LL) ϖ P (m k)))
  have e3 := hHor g hg (d k) (hd k)
  rw [e1, ← e2]
  exact congrArg _ (congrArg X e3)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCrystalStratificationMatrixStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_crystal_stratification_matrix : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := ↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  first | exact @GlobalTheory.CrysStrat.exists_stratification | exact GlobalTheory.CrysStrat.exists_stratification | (intros; apply GlobalTheory.CrysStrat.exists_stratification <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogUniformizerTiltBdRPlusCocycleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_uniformizerTilt_bdRPlus_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) → (∀ g, bk.FixFlat g → c g = 0) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∃ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) ∧ (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) := by
  first | (exact @GlobalTheory.LogFlatLam.exists_lam) | (exact GlobalTheory.LogFlatLam.exists_lam) | (intros; apply GlobalTheory.LogFlatLam.exists_lam  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisDividedTaylorExpansionFrobeniusBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_dividedTaylor_expansion_frobeniusBasis : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e) (g : ↥(GK (ϖ.field a))), ∃ Γ, (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)).IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩) := by
  first | exact @GlobalTheory.CrysGal.galois_taylor_basis | exact GlobalTheory.CrysGal.galois_taylor_basis | (intros; apply GlobalTheory.CrysGal.galois_taylor_basis <;> assumption)
end

