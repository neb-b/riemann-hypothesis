module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0683
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteLevelRecharacterised
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LevelRechar

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.LevGChar

section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {R : Type} [CommRing R]
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}


open Classical in
def dU (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) : Rˣ :=
  if h : IsUnit (red (NX.intLift v (NX.detT r x))) then h.unit else 1

theorem isUnit_red (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hdx : Valued.v (NX.detT r x) = 1) :
    IsUnit (red (NX.intLift v (NX.detT r x))) := by
  have hix : NX.detT r x ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdx]
  have ex : NX.intLift v (NX.detT r x) = ⟨_, hix⟩ := by rw [NX.intLift, dite_eq_left hix]
  rw [ex]; exact (isUnit_int hdx hix).map red

theorem dU_eq (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (h : IsUnit (red (NX.intLift v (NX.detT r x)))) : dU v red r x = h.unit := by
  unfold dU
  rw [dite_eq_left h]

theorem dU_mul (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L),
      Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (r : ℕ)
    (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (hx : NX.InParah v r x) (hy : NX.InParah v r y)
    (hdx : Valued.v (NX.detT r x) = 1) (hdy : Valued.v (NX.detT r y) = 1) :
    dU v red r (x * y) = dU v red r x * dU v red r y := by
  have hix : NX.detT r x ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdx]
  have hiy : NX.detT r y ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdy]
  have ex : NX.intLift v (NX.detT r x) = ⟨_, hix⟩ := by rw [NX.intLift, dite_eq_left hix]
  have ey : NX.intLift v (NX.detT r y) = ⟨_, hiy⟩ := by rw [NX.intLift, dite_eq_left hiy]
  have hxy : red (NX.intLift v (NX.detT r (x * y))) =
      red (NX.intLift v (NX.detT r x)) * red (NX.intLift v (NX.detT r y)) := by
    rw [ex, ey, ← map_mul]
    exact red_intLift red hred _ (by simpa using i_detT_mul v r x y hx hy)
  have hux := isUnit_red red r x hdx
  have huy := isUnit_red red r y hdy
  have huxy : IsUnit (red (NX.intLift v (NX.detT r (x * y)))) := by rw [hxy]; exact hux.mul huy
  rw [dU_eq red r _ hux, dU_eq red r _ huy, dU_eq red r _ huxy]
  exact Units.ext (by simp [hxy])

theorem dU_one (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L),
      Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (hx : ∀ a b, Valued.v (x a b - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) a b) < 1) :
    dU v red r x = 1 := by
  have hd : red (NX.intLift v (NX.detT r x)) = 1 := by
    rw [red_intLift red hred 1 (by simpa using i_detT_cong v r x hx), map_one]
  have hu : IsUnit (red (NX.intLift v (NX.detT r x))) := by rw [hd]; exact isUnit_one
  rw [dU_eq red r x hu]
  exact Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)

theorem exists_cong {ι : Type} [Fintype ι] (s : ι → SplitPlace L) : ∃ N : ℕ, 0 < N ∧ ∀ κ : GAf L n, NG.Cong L n N κ →
    ∀ t a b, Valued.v (NX.locM (s t) κ a b -
      (1 : Matrix (Fin n) (Fin n) ((s t).v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
  have hpos : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), 0 < Ideal.absNorm v.asIdeal := fun v =>
    Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hmem : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), Ideal.absNorm v.asIdeal ∣ N →
      (N : 𝓞 (maximalRealSubfield L)) ∈ v.asIdeal := fun v N h =>
    Ideal.mem_of_dvd _ (Nat.cast_dvd_cast h) (Ideal.absNorm_mem _)
  refine ⟨∏ t, Ideal.absNorm (s t).v.asIdeal, Finset.prod_pos fun _ _ => hpos _, fun κ hκ t => ?_⟩
  have hd : Ideal.absNorm (s t).v.asIdeal ∣ ∏ t, Ideal.absNorm (s t).v.asIdeal :=
    Finset.dvd_prod_of_mem (fun t => Ideal.absNorm (s t).v.asIdeal) (Finset.mem_univ t)
  exact locM_cong (s t) (hmem _ _ hd) κ hκ

end Loc

theorem mul_ringHom_units_ratio {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : B) (a a' : Aˣ) :
    p * f (a' : A) = p * f (a : A) * f ((a' * a⁻¹ : Aˣ) : A) := by
  rw [mul_assoc, ← map_mul, ← Units.val_mul, mul_comm a', mul_inv_cancel_left]

theorem exists_mul_hom {G H : Type} [Group G] [CommGroup H] {J : Subgroup G} (χ : J →* H) (c : G → H)
    (hc : ∀ κ κ' : J, c ((κ * κ' : J) : G) = c κ * c κ') : ∃ χ' : J →* H, ∀ κ : J, χ' κ = χ κ * c κ :=
  ⟨MonoidHom.mk' (fun κ => χ κ * c κ) (fun κ κ' => by rw [hc, map_mul, mul_mul_mul_comm]), fun _ => rfl⟩

theorem gVal_rechar (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ τ' : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (hu : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x)))) :
    NX.gVal D i k b kv s red τ' x = NX.gVal D i k b kv s red τ x *
      NX.toKk D i k (((τ' (dU s.v red D.R.r x) * (τ (dU s.v red D.R.r x))⁻¹ : (FractionRing (D.ntw.O i))ˣ)) :
        FractionRing (D.ntw.O i)) := by
  unfold NX.gVal
  rw [dite_eq_left hu, dite_eq_left hu, dU_eq red _ x hu]
  exact mul_ringHom_units_ratio _ _ _ _

theorem exists_rechar : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ τ' : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ), ∃ χ' : M.J →* (NX.Kk D i k)ˣ, (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ M.J, χ' ⟨κ, h⟩ = 1) ∧ NX.HypOutsideF M.J χ' (NX.badV D i Q) ∧ ∀ κ (h : κ ∈ M.J), ((χ' ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ' kv) (NX.locM (M.sp (NX.pG D kv)) κ)) * (∏ P ∈ M.QP, NX.ofOk D i k (NX.tameVal ψ P e (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) * (∏ P ∈ M.DP, NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e else -e) (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ τ' M
  classical
  have hred : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      ∀ z : (M.sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      Valued.v (z : (M.sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E)) < 1 → M.redG kv z = 0 := by
    intro kv z hz
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    exact i_red_zero _ (M.redG kv) z hz
  have hdet : ∀ (s : SplitPlace D.host.E) (κ : GAf D.host.E D.R.nV), κ ∈ Umax D.host.E D.R.nV →
      NX.InParah s.v D.R.r (NX.locM s κ) → Valued.v (NX.detT D.R.r (NX.locM s κ)) = 1 := fun s κ hU hp =>
    i_detT_one _ _ _ (NX.locM s κ⁻¹) (by rw [← locM_mul, mul_inv_cancel, locM_one]) (locM_int s (inv_mem hU)) hp
  obtain ⟨c, hc⟩ : ∃ c : GAf D.host.E D.R.nV → (NX.Kk D i k)ˣ, ∀ κ, c κ =
      ∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), Units.map (NX.toKk D i k).toMonoidHom
        (τ' kv (dU (M.sp (NX.pG D kv)).v (M.redG kv) D.R.r (NX.locM (M.sp (NX.pG D kv)) κ)) *
          (τ kv (dU (M.sp (NX.pG D kv)).v (M.redG kv) D.R.r (NX.locM (M.sp (NX.pG D kv)) κ)))⁻¹) := ⟨_, fun _ => rfl⟩
  have hmul : ∀ κ κ' : M.J, c ((κ * κ' : M.J) : GAf D.host.E D.R.nV) = c κ * c κ' := by
    rintro ⟨κ, hκ⟩ ⟨κ', hκ'⟩
    obtain ⟨h1, h2, -⟩ := (M.J_mem κ).1 hκ
    obtain ⟨h1', h2', -⟩ := (M.J_mem κ').1 hκ'
    show c (κ * κ') = c κ * c κ'
    rw [hc, hc, hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [locM_mul, dU_mul _ (hred kv) _ _ _ (h2 kv).1 (h2' kv).1 (hdet _ _ h1 (h2 kv).1) (hdet _ _ h1' (h2' kv).1),
      ← MonoidHom.map_mul, map_mul (τ kv), map_mul (τ' kv), mul_inv, mul_mul_mul_comm]
  have hone : ∀ κ : GAf D.host.E D.R.nV,
      (∀ kv a b, Valued.v (NX.locM (M.sp (NX.pG D kv)) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((M.sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) → c κ = 1 := by
    intro κ hg
    rw [hc]
    refine Finset.prod_eq_one fun kv _ => ?_
    rw [dU_one _ (hred kv) _ _ (hg kv), map_one, map_one, inv_one, mul_one, map_one]
  obtain ⟨χ', hχ'⟩ := exists_mul_hom M.χ c hmul
  have hχ : ∀ κ (h : κ ∈ M.J), χ' ⟨κ, h⟩ = M.χ ⟨κ, h⟩ * c κ := fun κ h => hχ' ⟨κ, h⟩
  refine ⟨χ', ?_, ?_, ?_⟩
  · obtain ⟨N, hN, hJ⟩ := M.J_open
    obtain ⟨N', hN', hc'⟩ := exists_cong (n := D.R.nV)
      (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => M.sp (NX.pG D kv))
    refine ⟨N * N', Nat.mul_pos hN hN', fun κ hκ => ?_⟩
    obtain ⟨h, h1⟩ := hJ κ hκ.of_mul_left
    refine ⟨h, ?_⟩
    have h2 : c κ = 1 := hone κ (hc' κ hκ.of_mul_right)
    rw [hχ, h1, h2, one_mul]
  · intro κ hκ
    refine ⟨(M.hyp κ hκ).1, fun h => ?_⟩
    rw [hχ, (M.hyp κ hκ).2 h, one_mul]
    refine hone κ fun kv a b => ?_
    have hw := (M.sp (NX.pG D kv)).w_under
    rw [M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))] at hw
    have hb : (M.sp (NX.pG D kv)).v ∈ NX.badV D i Q :=
      ⟨NX.pG D kv, hw, Or.inr (Or.inl ⟨kv.1, D.naut.plGw_over kv.1 kv.2⟩)⟩
    rw [locM_triv _ hκ hb]
    simp
  · intro κ h
    obtain ⟨h1, h2, -⟩ := (M.J_mem κ).1 h
    rw [hχ, Units.val_mul, M.chi_eq κ h, hc, Units.coe_prod,
      Finset.prod_congr rfl fun kv _ => gVal_rechar D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (τ' kv) _
        (isUnit_red _ _ _ (hdet _ _ h1 (h2 kv).1)), Finset.prod_mul_distrib]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring

end GlobalTheory.LevelRechar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeoExtN
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.StateChecks

namespace GlobalTheory.HeightCounting.SerMove.ReGeo

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {hX : B.fields.Ok} {Wt : Set B.places.Pl}


set_option maxHeartbeats 4000000 in
theorem geo_copy {Z Z' : w.Lt} (z₀ : Dat (w.st Z) w.I hX T Wt) (z : Dat (w.st Z') w.I hX T Wt) (h1 : z.Xg = z₀.Xg)
    (h2 : z.tr = z₀.tr) (h3 : HEq z.core (coreJ (a := Z) Z' z₀.core)) (h4 : HEq z.R (real3 (a := Z) Z' (iK := z₀.alg) z₀.R))
    (hg : GlobalTheory.RealGeo.InGeo z₀.geo) :
    ∃ g : GlobalTheory.RealGeo.GeoHalf z.core z.R.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo g ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z₀ z' → ExtN { z with geo := g } z') ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z' z₀ → ExtN z' { z with geo := g }) := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4 ⊢
  subst h1 h2
  obtain rfl : core = coreJ (a := Z) Z' z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg (a := Z) Z' z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR (a := Z) Z' z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR (a := Z) Z' z₀)) :))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · with_unfolding_all
      exact GlobalTheory.Mem.R3.Tr.geoHalf (a := Z) Z' (iK := z₀.alg) z₀.geo
  · with_unfolding_all
      exact GlobalTheory.Mem.R3.Tr.inGeo_tr (a := Z) Z' (iK := z₀.alg) hg
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }

end GlobalTheory.HeightCounting.SerMove.ReGeo

namespace GlobalTheory.HeightCounting.SerMove

theorem exists_geo_extN : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}, Ext P.z P'.z → ∀ (x : St P) (x' : St P'), ∃ (g : Geo x) (g' : Geo x'), GlobalTheory.RealGeo.InGeo g ∧ GlobalTheory.RealGeo.InGeo g' ∧ ExtN (datAt x g) (datAt x' g') := by
  intro K B B' f f' T T' w w' P P' e x x'
  obtain ⟨g, hg, hL, -⟩ := ReGeo.geo_copy (Z := P.Z₀) (Z' := x.o.Z) P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.inGeo
  obtain ⟨g', hg', -, hR⟩ :=
    ReGeo.geo_copy (Z := P'.Z₀) (Z' := x'.o.Z) P'.z x'.m.z x'.m.Xg x'.m.tr ((by with_unfolding_all exact (x'.copy.core :))) ((by with_unfolding_all exact (x'.copy.R :))) P'.inGeo
  exact ⟨g, g', hg, hg', hR _ (hL _ e.extN)⟩

end GlobalTheory.HeightCounting.SerMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralObjectsOverReplacedStages
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.SRe

section Parts

variable {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
  {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
  {F0 : ∀ u, Forms0 a.D u} (P : SPack a.D F0) {F₁ : ∀ u, Forms0 (reL a Z).D u} (hs : SameL a Z F0 F₁)
  (hF : FinX (reY Z P.Y))


set_option maxHeartbeats 4000000 in
def packL : SPack (reL a Z).D F₁ := (by with_unfolding_all exact ((P.re Z hs hF) :))


set_option maxHeartbeats 4000000 in
def restL (S : SRest (P.re Z hs hF)) : SRest (packL a Z P hs hF) := (by with_unfolding_all exact (S :))


set_option maxHeartbeats 4000000 in
theorem restL_j (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) :
    (restL a Z P hs hF S).j = (by with_unfolding_all exact (j.trans (eEECre Z P.G) :)) := (by with_unfolding_all exact (hS :))


set_option maxHeartbeats 4000000 in
theorem nonempty_sAtL (R : RealDat a.D A Ks) (F : Face a.D A) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H)
    (t : GA a.D (a.D.sp.Y 0)) (c : ℝ) (hc : 0 < c) (see : SeeAt R F P.X P.inst t)
    (ev : EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c)
    (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (rowJ : RowJ R eE P.X P.inst P.G t j)
    (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) : Nonempty (SAtL a Z R F eE F₁) := by
  have h1 := mvRowJ a Z R P.X P.inst P.G t eE j rowJ
  have h2 := restL_j a Z P hs hF j S hS
  letI := alg (reL a Z) iK
  exact ⟨{ P := packL a Z P hs hF
           S := restL a Z P hs hF S
           t := tL a Z t
           c := c
           c_pos := hc
           see := (by with_unfolding_all exact ((mvSee a Z R F P.X P.inst t see) :))
           ev := (by with_unfolding_all exact ((mvEv_holds a Z R F P.X P.inst P.G t c ev) :))
           rowJ := by rw [h2]; exact (by with_unfolding_all exact (h1 :)) }⟩

end Parts


set_option maxHeartbeats 4000000 in
theorem satOfDiscreteSeries : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (P : SPack a.D F0), GapHyp a.D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D → a.D.what₂.Dstar = StandardLattice.DstarD a.D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed a.D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ R F eE F₁) := by
  intro h1 h2 h3 h4 h5 B C a G' _ _ Pl0 T A Ks _ _ _ R F F0 eE P hG hI hL hRT hDs hLev hgl hPin hE0 hMod hRg hN hDall
  obtain ⟨hD, j, t, c, hc, see, ev, rowJ, rest⟩ := _root_.GlobalTheory.Mem.SRe.exists_sRest_top h1 h2 h3 h4 h5 a.D G' Pl0 T A Ks R F F0 P eE hG hI hL hRT hDs
    hLev hgl hPin hE0 hMod hRg hN hDall
  refine ⟨P.toNew hD j, fun N hh F₁ hs => ?_⟩
  obtain ⟨hF, S, hS⟩ := rest N hh _ hs
  exact nonempty_sAtL a _ P hs hF R F eE t c hc see ev j rowJ S hS

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHomEqOfFramesKeepMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FrameFinPart

theorem finHom_eq_of_idFrame : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P P' : principalLevelFrame.RowPsi V n), GlobalTheory.MtRead.IdFrame hF P → GlobalTheory.MtRead.IdFrame hF P' → ∀ g, (finHom V).rangeRestrict (P.ψ g) = (finHom V).rangeRestrict (P'.ψ g) := by
  intro D V n hF P P' hP hP' g
  obtain ⟨hn, h⟩ := hP
  obtain ⟨hn', h'⟩ := hP'
  apply Subtype.ext
  apply Units.ext
  ext a b
  change finMat D.sp.cm.sig V.gram (P.ψ g) a b = finMat D.sp.cm.sig V.gram (P'.ψ g) a b
  rw [h, h']

end GlobalTheory.FrameFinPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedConstructionStatesCharactersAgree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.LevExt

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove

theorem frat_delAt_heq {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'} (hP : B'.toPre = B.toPre)
    {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) (l : ℕ) :
    HEq ((Top.Fr.at a'.st f').delAt l) ((Top.Fr.at a.st f).delAt l) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).delAt l)) :))


set_option maxHeartbeats 4000000 in
theorem chars_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Chars (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hP : B'.toPre = B.toPre := l.enl.1
  have hC : x.m.z.R.toLevCh.C = Top.Fr.at (w.st x.o.Z) f := x.m.z.lev.C.trans (by rw [w.C_eq])
  have hC' : x'.m.z.R.toLevCh.C = Top.Fr.at (w'.st x'.o.Z) f' := x'.m.z.lev.C.trans (by rw [w'.C_eq])
  have hs := x.m.z.lev.is
  have hs' := x'.m.z.lev.is
  have hm : (Dof x').R.m = (Dof x).R.m := by
    exact congrArg (fun p : Pre => p.R.m) hP
  have hmu0 : ∀ (i : Fin (Dof x).R.m) (i' : Fin (Dof x').R.m), (i : ℕ) = i' →
      HEq (x'.m.z.R.toLevCh.C.mu0 i') (x.m.z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr h
  refine ⟨?_, fun j => ?_, fun j j' h => ?_, fun l0 => ?_⟩
  · have heta : HEq x'.m.z.R.toLevCh.C.eta x.m.z.R.toLevCh.C.eta := by
      rw [hC, hC']
      exact frat_eta_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP heta hs.eta hs'.eta).symm
  · let j' : Fin (Dof x').R.m := ⟨j, lt_of_lt_of_eq j.2 hm.symm⟩
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP (hmu0 j j' rfl) (hs.mu0 j) (hs'.mu0 j')).symm
  · exact (hmu0 j j' h).symm
  · show HEq (x.m.z.R.toLevCh.C.delAt l0) (x'.m.z.R.toLevCh.C.delAt l0)
    rw [hC, hC']
    exact (frat_delAt_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr l0).symm

end GlobalTheory.HeightCounting.SerMove

end
end

