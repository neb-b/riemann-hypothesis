module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysLatticeBasisMemSumDeRhamFiltration
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplementOfCharactersUniqueUpToConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.CharCancel

section Cancel

variable {K Γ V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem ennreal_volume_ratio_step_cancel (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (c : Γ → K) (e : (V × K) ≃ₗ[K] (W × K))
    (h : ∀ g v x, e (a g v, c g * x) = (b g (e (v, x)).1, c g * (e (v, x)).2))
    (v₀ : V) (hv : ∀ g, a g v₀ = c g • v₀) (hd : (e (v₀, 1)).2 ≠ 0) :
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  rcases hE : e (v₀, 1) with ⟨w', δ⟩
  have hd0 : δ ≠ 0 := by rw [hE] at hd; exact hd
  have hb : ∀ g, b g w' = c g • w' := by
    intro g
    have h1 := h g v₀ 1
    have h2 : ((a g v₀, c g * 1) : V × K) = c g • ((v₀, 1) : V × K) := by
      rw [hv]; simp
    rw [h2, map_smul, hE] at h1
    have h3 := congrArg Prod.fst h1
    simp at h3
    exact h3.symm
  refine ⟨{ toFun := fun v => (e (v, 0)).1 - ((e (v, 0)).2 / δ) • w'
            invFun := fun w => (e.symm (w, 0)).1 - (e.symm (w, 0)).2 • v₀
            map_add' := ?_, map_smul' := ?_, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · intro x y
    have hxy : ((x + y, (0 : K)) : V × K) = (x, 0) + (y, 0) := by simp
    rw [hxy, map_add (f := _)]
    simp only [Prod.fst_add, Prod.snd_add, add_div, add_smul]
    abel
  · intro s x
    have hsx : ((s • x, (0 : K)) : V × K) = s • (x, 0) := by simp
    rw [hsx, map_smul]
    simp [smul_sub, smul_smul, mul_div_assoc]
  · intro v
    dsimp only
    have key : (((e (v, 0)).1 - ((e (v, 0)).2 / δ) • w', (0 : K)) : W × K) =
        e (v, 0) - ((e (v, 0)).2 / δ) • e (v₀, 1) := by
      rw [hE]
      ext
      · simp
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        rw [div_mul_cancel₀ _ hd0, sub_self]
    rw [key, map_sub, map_smul, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    simp
  · intro w
    dsimp only
    have key : (((e.symm (w, 0)).1 - (e.symm (w, 0)).2 • v₀, (0 : K)) : V × K) =
        e.symm (w, 0) - (e.symm (w, 0)).2 • (v₀, 1) := by
      ext <;> simp
    rw [key, map_sub, map_smul, LinearEquiv.apply_symm_apply, hE]
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, zero_sub]
    rw [neg_div, mul_div_cancel_right₀ _ hd0, neg_smul, sub_neg_eq_add, sub_add_cancel]
  · intro g v
    show (e (a g v, 0)).1 - ((e (a g v, 0)).2 / δ) • w' = b g ((e (v, 0)).1 - ((e (v, 0)).2 / δ) • w')
    have h1 := h g v 0
    rw [mul_zero] at h1
    rw [h1, map_sub, map_smul, hb, smul_smul]
    dsimp only
    rw [show c g * (e (v, 0)).2 / δ = (e (v, 0)).2 / δ * c g by ring]

theorem cancel_one (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (c : Γ → K) (e : (V × K) ≃ₗ[K] (W × K))
    (h : ∀ g v x, e (a g v, c g * x) = (b g (e (v, x)).1, c g * (e (v, x)).2)) :
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  by_cases hd : (e ((0 : V), (1 : K))).2 = 0
  · rcases hq : e.symm ((0 : W), (1 : K)) with ⟨v₁, d'⟩
    have hq' : e (v₁, d') = ((0 : W), (1 : K)) := by rw [← hq]; simp
    have hv1 : ∀ g, a g v₁ = c g • v₁ := by
      intro g
      have h1 := h g v₁ d'
      rw [hq'] at h1
      simp only [map_zero, mul_one] at h1
      have h2 : e (c g • v₁, c g * d') = ((0 : W), c g) := by
        have h3 : ((c g • v₁, c g * d') : V × K) = c g • (v₁, d') := by simp
        rw [h3, map_smul, hq']; simp
      have h4 := e.injective (h1.trans h2.symm)
      simpa using congrArg Prod.fst h4
    have hd1 : (e (v₁, 1)).2 ≠ 0 := by
      have h5 : ((v₁, 1) : V × K) = (v₁, d') + (1 - d') • ((0 : V), (1 : K)) := by ext <;> simp
      rw [h5, map_add (f := _), map_smul, hq']
      simp [hd]
    exact ennreal_volume_ratio_step_cancel a b c e h v₁ hv1 hd1
  · exact ennreal_volume_ratio_step_cancel a b c e h 0 (fun g => by simp) hd

def splitFirst (V : Type) [AddCommGroup V] [Module K V] (t : ℕ) :
    ((V × (Fin t → K)) × K) ≃ₗ[K] (V × (Fin (t + 1) → K)) where
  toFun p := (p.1.1, Fin.cons p.2 p.1.2)
  invFun q := ((q.1, fun j => q.2 j.succ), q.2 0)
  map_add' p q := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  map_smul' x p := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  left_inv p := by simp
  right_inv q := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem cancel_fin (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (t : ℕ) :
    ∀ (c : Fin t → Γ → K) (e : (V × (Fin t → K)) ≃ₗ[K] (W × (Fin t → K))),
    (∀ g v x, e (a g v, fun j => c j g * x j) = (b g (e (v, x)).1, fun j => c j g * (e (v, x)).2 j)) →
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  induction t with
  | zero =>
    intro c e h
    refine ⟨((LinearEquiv.prodUnique : (V × (Fin 0 → K)) ≃ₗ[K] V).symm.trans e).trans
      (LinearEquiv.prodUnique : (W × (Fin 0 → K)) ≃ₗ[K] W), fun g v => ?_⟩
    have hx : ((a g v, fun j => c j g * (default : Fin 0 → K) j) : V × (Fin 0 → K)) = (a g v, default) :=
      Prod.ext rfl (Subsingleton.elim _ _)
    have h1 := h g v default
    rw [hx] at h1
    show (e (a g v, default)).1 = b g (e (v, default)).1
    rw [h1]
  | succ t ih =>
    intro c e h
    let S := splitFirst (K := K) V t
    let T := splitFirst (K := K) W t
    let a' : Γ → (V × (Fin t → K)) →ₗ[K] (V × (Fin t → K)) := fun g =>
      (a g).prodMap (LinearMap.pi fun j => c j.succ g • LinearMap.proj j)
    let b' : Γ → (W × (Fin t → K)) →ₗ[K] (W × (Fin t → K)) := fun g =>
      (b g).prodMap (LinearMap.pi fun j => c j.succ g • LinearMap.proj j)
    refine (cancel_one a' b' (c 0) ((S.trans e).trans T.symm) ?_).elim fun f' hf' => ?_
    · intro g p y
      obtain ⟨v, x⟩ := p
      have hS : ∀ (u : V) (z : Fin t → K) (s : K), S ((u, z), s) = (u, Fin.cons s z) := fun _ _ _ => rfl
      have hT : ∀ q : W × (Fin (t + 1) → K), T.symm q = ((q.1, fun j => q.2 j.succ), q.2 0) := fun _ => rfl
      have ha : a' g (v, x) = (a g v, fun j => c j.succ g * x j) := rfl
      have hcons : (Fin.cons (c 0 g * y) (fun j => c j.succ g * x j) : Fin (t + 1) → K) =
          fun j => c j g * (Fin.cons y x : Fin (t + 1) → K) j := by
        funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp
      simp only [LinearEquiv.trans_apply]
      rw [ha, hS, hS, hcons, h g v (Fin.cons y x : Fin (t + 1) → K), hT, hT]
      rfl
    · exact ih (fun j => c j.succ) f' (fun g v x => hf' g (v, x))

end Cancel

theorem overK_apply {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {k : ℕ}
    (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := by
  simp [overK, mat, toFr, matRep, mapM]

theorem conj_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ σ' : Γ →* GL (Fin n) A) (ρ ρ' : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (hP : ∃ Pm : GL (Fin n) (FractionRing A), ∀ g,
      (Pm : Matrix (Fin n) (Fin n) (FractionRing A)) * (mat σ g).map (toFr A) =
        (mat σ' g).map (toFr A) * (Pm : Matrix (Fin n) (Fin n) (FractionRing A)))
    (h : ∃ e, IsDecomp (t := t) σ ρ χ e) (h' : ∃ e, IsDecomp (t := t) σ' ρ' χ e) :
    ∃ Pm : GL (Fin r) (FractionRing A), ∀ g,
      (Pm : Matrix (Fin r) (Fin r) (FractionRing A)) * (mat ρ g).map (toFr A) =
        (mat ρ' g).map (toFr A) * (Pm : Matrix (Fin r) (Fin r) (FractionRing A)) := by
  obtain ⟨Pm, hPm⟩ := hP
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  let L : (Fin n → FractionRing A) ≃ₗ[FractionRing A] (Fin n → FractionRing A) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' (Pm : Matrix (Fin n) (Fin n) (FractionRing A)))
      (Matrix.toLin' ((Pm⁻¹ : GL (Fin n) (FractionRing A)) : Matrix (Fin n) (Fin n) (FractionRing A)))
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
  have hL : ∀ g u, L (overK σ g u) = overK σ' g (L u) := by
    intro g u
    simp only [L, LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply, overK_apply, Matrix.mulVec_mulVec, hPm g]
  refine (cancel_fin (fun g => overK ρ g) (fun g => overK ρ' g) t
    (fun j g => toFr A ((χ (↑j + 1) g : Aˣ) : A)) ((e.symm.trans L).trans e') ?_).elim fun f hf => ?_
  · intro g v x
    have he1 := he g (e.symm (v, x))
    simp only [LinearEquiv.apply_symm_apply] at he1
    have h2 : e.symm (overK ρ g v, fun j => toFr A ((χ (↑j + 1) g : Aˣ) : A) * x j) = overK σ g (e.symm (v, x)) := by
      rw [← he1, LinearEquiv.symm_apply_apply]
    simp only [LinearEquiv.trans_apply]
    rw [h2, hL, he']
  · refine ⟨⟨LinearMap.toMatrix' (f : (Fin r → FractionRing A) →ₗ[FractionRing A] (Fin r → FractionRing A)),
      LinearMap.toMatrix' (f.symm : (Fin r → FractionRing A) →ₗ[FractionRing A] (Fin r → FractionRing A)), ?_, ?_⟩,
      fun g => ?_⟩
    · rw [← LinearMap.toMatrix'_comp]; simp
    · rw [← LinearMap.toMatrix'_comp]; simp
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
        Matrix.toLin'_apply, ← overK_apply, LinearEquiv.coe_coe]
      exact hf g v

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (r π)) → (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r π g).map (toK N i) = (rO N i r' π g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → (∃ e, IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → (∃ e, IsDecomp (t := R.t) (r' π) (ρ' π) (N.chi i) e) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) := by
  intro R H what₂ N i r r' ρ ρ' π _ hP h h'
  exact conj_of_isDecomp (r π) (r' π) (ρ π) (ρ' π) (N.chi i) hP h h'

end GlobalTheory.CharCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysLatticeBasisMemSumDeRhamFiltrationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crysLattice_basis_mem_sum_deRham_filtration : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → Per.BdR l) (v : Fin m → Fin d → Per.BdR l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → Per.BdR l) = ∑ i, c i • v i := by
  first | exact @GlobalTheory.crysLattice_basis_mem_sum_fil_dR | exact GlobalTheory.crysLattice_basis_mem_sum_fil_dR | (intros; apply GlobalTheory.crysLattice_basis_mem_sum_fil_dR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem crysOnCond_all : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), CrysOnCond D HW F :=
  fun D HW _ l _ K s LL h Y hY => GlobalTheory.CrysOnLevel.isCrysOn_of_isCrys D HW l K s LL h Y hY

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.Per.CharJumps

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_act (g : G) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g w) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, AlgebraTensorModule.map_tmul, PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_mem_DdR {w : V ⊗[Qp] B} (hw : w ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) w ∈ DdR PD ρ := by
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hw ⊢
  intro g
  rw [← ιV_act, hw g]

theorem ιV_mul (a : K₀) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (B := B) (V := V) (LL := LL) a w) =
      mulVdR (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K a) (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, mulVB, mulVdR, AlgebraTensorModule.map_tmul, ← IsScalarTower.algebraMap_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_mem_DdRE (hs : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    {w : V ⊗[Qp] B} (hw : w ∈ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) :
    ιV PD (LL := LL) (V := V) w ∈ DdRE PD ρ τ := by
  unfold DcrisL at hw
  unfold DdRE
  rw [Submodule.mem_inf] at hw ⊢
  refine ⟨ιV_mem_DdR PD ρ hw.1, ?_⟩
  have h2 := hw.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  obtain ⟨a, rfl⟩ := hs c
  rw [← ιV_mul, h2 a, map_smul]
  simp

theorem FilV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v s =>
    exact ⟨v ⊗ₜ ⟨(s : BdR), PD.Fil_anti a s.2⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem FilV_anti : Antitone fun a : ℤ => FilV PD (LL := LL) (V := V) a :=
  antitone_int_of_succ_le (FilV_succ_le PD)

end General

end GlobalTheory.Per.CharJumps

namespace GlobalTheory.Per.CharJumps

theorem inf_of_line {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M] (D : Submodule LL M)
    (hD : finrank LL ↥D = 1) (F : ℤ → Submodule LL M) (hF : Antitone F) {x : M} (hx : x ∈ D)
    (d : ℤ) (h1 : x ∈ F d) (h2 : x ∉ F (d + 1)) (b : ℤ) :
    D ⊓ F b = if b ≤ d then D else ⊥ := by
  have hx0 : x ≠ 0 := fun h => h2 (h ▸ (F (d + 1)).zero_mem)
  have hspan : ∀ y ∈ D, ∃ c : LL, c • x = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hx⟩ : ↥D)
      (fun h => hx0 (congrArg Subtype.val h))).1 hD ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  split_ifs with hb
  · refine inf_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := hspan y hy
    exact (F b).smul_mem c (hF hb h1)
  · rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨c, rfl⟩ := hspan _ hy.1
    rw [Submodule.mem_bot]
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply h2
      have hxe : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hxe]
      exact hF (by omega) ((F b).smul_mem _ hy.2)

theorem jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  intro l _ P AI T K LL hA μ hμ d hw hcrys τ b
  haveI := LL.2
  haveI := K.2
  have hdr : IsDR (P.PD K) (charRep μ) := by
    let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      { V := ↥LL.1, ρ := charRep μ,
        cont := fun x => by
          show Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1) • LinearMap.id x
          exact hμ.smul continuous_const }
    exact ((GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI T K) ↥LL.1 ↥(OL LL)
      (GlobalTheory.LocalIntegers.good_integers l LL).1 A).2.2 hcrys
  obtain ⟨-, -, hdim⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)).1 τ
  set_option synthInstance.maxHeartbeats 200000 in
  have h1 : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdim hdr, Module.finrank_self]
  have hs : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun c => ⟨⟨c.1, c.2, hA.1 c.2⟩, rfl⟩
  obtain ⟨w, hwD, hin, hout⟩ := hw τ
  have hx := ιV_mem_DdRE (P.PD K) (charRep μ) hs τ hwD
  have key := inf_of_line _ h1 _ (FilV_anti (P.PD K)) hx (d τ) hin hout
  have fk : ∀ c : ℤ, (finrank ↥LL.1 ↥(FildR (P.PD K) (charRep μ) τ c) : ℤ) = if c ≤ d τ then 1 else 0 := by
    intro c
    unfold FildR
    rw [key c]
    by_cases hc : c ≤ d τ
    · rw [if_pos hc, if_pos hc, h1]
      rfl
    · rw [if_neg hc, if_neg hc, finrank_bot]
      rfl
  unfold multV
  rw [fk b, fk (b + 1)]
  split_ifs <;> omega

end GlobalTheory.Per.CharJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSumStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ i : Let K, Set.BijOn (φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) (Di (HW l) h T (i - 1)) (Di (HW l) h T i)) ∧ (⨆ i : Let K, Di (HW l) h T i) = Dcris ((D.loc l).PD K) T.ρ ∧ iSupIndep (fun i : Let K => Di (HW l) h T i) ∧ Function.Injective (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  first | exact @GlobalTheory.NL.PhiD.phi_letters | exact GlobalTheory.NL.PhiD.phi_letters | (intros; apply GlobalTheory.NL.PhiD.phi_letters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.ResFinite

theorem adm12_elementDenominator : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm12 D := by
  intro D l _ K K' hKK hle LL T hc
  have hT := D.locT l
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) hT K' LL T.V T.ρ hc).1
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (D.loc l) (D.locA l) hT K' K LL hKK T.V T.ρ).1 hc
  · intro τ a
    exact _root_.GlobalTheory.JumpRestrict.multV_restrict l (D.loc l) (D.locA l) hT K' K LL hKK T.V T.ρ hdr τ a

end GlobalTheory.Per.ResFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltrationStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamComponent_wachLetter_basis_filtration : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ ι, Comp (HW l) h i ζ τ ι → τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb i → (∀ (r : ℕ) (d : Fin r → T.V ⊗[ℚ_[l]] (D.loc l).R.B) (b : Fin r → (D.loc l).R.BdR), (∀ a, d a ∈ Di (HW l) h T i) → LinearIndependent ↥LL.1 d → ∑ a, mulVR T (b a) (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (d a)) ∈ compKer T ι → ∀ a, b a = 0) ∧ (∀ d ∈ Di (HW l) h T i, ∀ a : ℤ, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ↔ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ compKer T ι ⊔ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) a) ∧ (∀ w ∈ DdRE ((D.loc l).PD K) T.ρ τ, ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ') ∧
    @Module.finrank ↥LL.1 ↥(Di (HW l) h T i) _ (Submodule.addCommMonoid _) (Submodule.module _) =
      Module.finrank ↥LL.1 T.V := by
  intro D HW l _ K s LL h W T hT i ζ τ ι hC hτ
  obtain ⟨-, -, -, hc, hc0⟩ := Points.points D HW l K s LL h
  exact GlobalTheory.NL.CompD.component_tied (D.locT l) K LL T hc hc0 hT τ ι hC.2.2 _ hτ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingData
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.AdmDepthZero

theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → PairedCharacterCondition.admDZ P := by
  intro D P h i k v PI τ hτ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro hsq hu
  obtain ⟨ρ, hρ, he⟩ := _root_.GlobalTheory.PrimCentIdem.main (D.host.g k) D.R.r (P.lz k) τ
  have hO := PairedCharacterCondition.RT.ktyTie_of_spec P i PI k v τ hτ
  rw [he] at hO
  have hs : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k ((P.lz k).lab τ) =
      Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
    rw [← he]
    exact PairedCharacterCondition.RT.idem_mul_eSer P k τ
  exact h i k v PI ρ _ hρ hs hO hsq hu

end GlobalTheory.AdmDepthZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescNEqXPowMulIterateDerivative
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal

theorem coeff_iterate_derivative_descFactorial (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) (m : ℕ) :
    coeff m (d⁄dX^[p] f) = ((m + p).descFactorial p : K) * coeff (m + p) f := by
  rw [PowerSeries.coeff_iterate_derivative, Nat.add_descFactorial_eq_ascFactorial]

theorem descN_eq_X_pow_mul_iterate_derivative :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧), descN K p f = X ^ p * d⁄dX^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative_descFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega), Nat.cast_zero, zero_mul]

end GlobalTheory.BKReal
end

