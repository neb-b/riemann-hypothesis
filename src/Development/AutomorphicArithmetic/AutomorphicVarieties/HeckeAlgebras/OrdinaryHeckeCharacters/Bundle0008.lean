module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.EqOnTors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HeckeDeterminantReductionEqResidual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.heckeDeterminant_reduction_eq_residual :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : HD Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ D : W.GDet n T V.frame.G₀, D.IsCont (maximalIdeal T) →
    (∀ (w : (hset Q R.τ₀).Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
      D.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    D.map (Alg.res c.O T : T →+* ResidueField c.O) = r.Dbar := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hA T _ _ _ gen hgen D hD hF
  refine JEx.red_eq r D hD _ hA.dense ?_
  rintro g ⟨w, hw, B, σ, hB, hσ, rfl⟩
  have h1 := hF ⟨w, hw⟩ B σ hB hσ
  have h2 := R.res.frob ⟨w, hw⟩ B σ hB hσ
  refine (congrArg (Polynomial.map _) h1).trans (Eq.trans ?_ h2.symm)
  rw [JEx.heckePol_map]
  congr 1
  funext j
  split_ifs with h
  · have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inl (⟨w, hw⟩, ⟨j - 1, h.2⟩)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    exact h3
  · exact map_one _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HeckeDeterminantSatisfiesDeformationRelations
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.heckeDeterminant_satisfies_deformation_relations :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (T : Type) [CommRing T] [Algebra c.O T] (D : W.GDet n T V.frame.G₀) (ψ : ∀ v : V.frame.Vl, Fin n → V.frame.Gv v →* Tˣ) (Gd : (T →ₐ[c.O] Qbar l) → Prop),
    (∀ t : T, (∀ x, Gd x → x t = 0) → t = 0) →
    (∀ x, Gd x → ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), PU r ι lam ρ ∧ D.map x.toRingHom = W.GDet.ofRep (W.mat ρ) ∧ ∀ v, W.HasFlag (ρ.comp (V.frame.φ v)) fun i => W.pushCh x.toRingHom (ψ v i)) →
    (∀ i g, D.lam i (V.frame.star c.O T n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)) ∧
    (∀ v (g : Fin n → V.frame.Gv v) (h : V.frame.G₀), D.tr (MonoidAlgebra.single h 1 * V.frame.oEl v (ψ v) g) = 0) ∧
    ∀ u, ∀ g ∈ r.Ip u, ∀ h : V.frame.G₀, D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V c r ι lam T _ _ D ψ Gd hsep hex
  choose ρ hPU hD hfl using hex
  obtain ⟨hP, hO, hI⟩ := JEx.rels V.frame c.O T D ψ (X := {x // Gd x}) (Qbar l) (fun x => x.1) (fun x => ρ x.1 x.2)
    (fun a ha => hsep a fun x hx => ha ⟨x, hx⟩) (fun x => hD x.1 x.2) (fun x => (hPU x.1 x.2).form) (fun x => hfl x.1 x.2)
  refine ⟨(AlgebraTools.Det.polarIffLam _ _ _ _ D).1 hP, fun v g h => AlgebraTools.Det.killsLam D _ (hO v g) _ 1 le_rfl hn,
    fun u g hg h => AlgebraTools.Det.killsLam D _ (hI g fun x => ?_) _ 1 le_rfl hn⟩
  obtain ⟨t, ht, ht1⟩ := JEx.teich c r
  obtain ⟨a, ha⟩ := (hPU x.1 x.2).type t ht u
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have h1 : a * ρ x.1 x.2 g * a⁻¹ = 1 := by
    refine Units.ext ((ha g hg1).trans ?_)
    have e : ∀ i, t i g = 1 := fun i => ht1 i g (Subgroup.mem_iInf.1 hg2 i)
    simp only [e, Units.val_one, map_one, Matrix.diagonal_one]
  exact conj_eq_one_iff.1 h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiAlgUnit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem hiAlg_unit {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] (Y L : Submodule A M)
    [Module.Finite A Y] [Module.Finite A L] (hLY : L ≤ Y) (op : ι → Module.End A M) [h : Fact (CommOn L op)] (i : ι)
    (hb : Set.BijOn (op i) Y Y) : IsUnit (heckeGen L op i) := by
  have hYs : ∀ y ∈ Y, op i y ∈ Y := fun y hy => hb.mapsTo hy
  let fY : Module.End A Y := (op i).restrict hYs
  have hfYb : Function.Bijective fY := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hb.injOn x.2 y.2 (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, hxy⟩ := hb.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨u, hu⟩ := (Module.End.isUnit_iff fY).2 hfYb
  have hinv : ((u⁻¹ : (Module.End A Y)ˣ) : Module.End A Y) ∈ Algebra.adjoin A ({fY} : Set (Module.End A Y)) :=
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.invMem A Y _ u (by rw [hu]; exact Algebra.subset_adjoin rfl)
  have hpres : ∀ g ∈ Algebra.adjoin A ({fY} : Set (Module.End A Y)), ∀ y : Y, (y : M) ∈ L → ((g y : Y) : M) ∈ L := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      intro y hy
      exact h.out.1 i y hy
    | algebraMap r =>
      intro y hy
      simpa using L.smul_mem r hy
    | add x z _ _ hx hz =>
      intro y hy
      simpa using L.add_mem (hx y hy) (hz y hy)
    | mul x z _ _ hx hz =>
      intro y hy
      exact hx _ (hz y hy)
  have hgL : Function.Bijective (heckeGen L op i : Module.End A L) := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hb.injOn (hLY x.2) (hLY y.2) (congrArg Subtype.val hxy)
    · intro y
      refine ⟨⟨(((u⁻¹ : (Module.End A Y)ˣ) : Module.End A Y) ⟨y, hLY y.2⟩ : M), hpres _ hinv _ y.2⟩, ?_⟩
      apply Subtype.ext
      have h1 := LinearMap.congr_fun u.mul_inv ⟨y, hLY y.2⟩
      rw [hu] at h1
      have h2 := congrArg Subtype.val h1
      exact h2
  obtain ⟨v, hv⟩ := (Module.End.isUnit_iff _).2 hgL
  have hmem : ((v⁻¹ : (Module.End A L)ˣ) : Module.End A L) ∈ heckeAlg L op :=
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.invMem A L (heckeAlg L op) v (by rw [hv]; exact (heckeGen L op i).2)
  refine ⟨⟨heckeGen L op i, ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show (heckeGen L op i : Module.End A L) * _ = 1
    rw [← hv]
    exact v.mul_inv
  · apply Subtype.ext
    show _ * (heckeGen L op i : Module.End A L) = 1
    rw [← hv]
    exact v.inv_mul

private theorem hiAlg_top {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] (L : Submodule A M)
    (op : ι → Module.End A M) [h : Fact (CommOn L op)] : Algebra.adjoin A (Set.range (heckeGen L op)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨x, hx⟩ -
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj⟩ := hx
    have he : (⟨x, Algebra.subset_adjoin ⟨j, hj⟩⟩ : heckeAlg L op) = heckeGen L op j := by
      apply Subtype.ext
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      exact hj y
    rw [he]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem _ r
  | add x z hx' hz' hx hz =>
    exact Subalgebra.add_mem _ hx hz
  | mul x z hx' hz' hx hz =>
    exact Subalgebra.mul_mem _ hx hz

private theorem hiAlg_abs {O A M ι : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing A] [Algebra O A]
    [Alg.IsCO O A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → O)
    (hc : CommOn Y op) (L : Submodule A M) (hL : L = locPart Y op fun i => algebraMap O A (a i)) [Fact (CommOn L op)] (hne : L ≠ ⊥)
    [Algebra O (heckeAlg L op)] [IsScalarTower O A (heckeAlg L op)] :
    ∃ _ : Alg.IsCO O (heckeAlg L op), (algebraMap A (heckeAlg L op)).Finite ∧
      (∀ b : A, (∀ y ∈ Y, b • y = 0 → y = 0) → ∀ t, algebraMap A (heckeAlg L op) b * t = 0 → t = 0) ∧
      (∀ i, heckeGen _ op i - algebraMap O (heckeAlg L op) (a i) ∈ maximalIdeal _) := by
  haveI : IsCNL A := IsCNL.ofCO O A
  subst hL
  obtain ⟨hT, hfin, hloc, hres, hgen, hnzd⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeLocal A M ι Y op
    (fun i => algebraMap O A (a i)) hc hne (heckeAlg (locPart Y op fun i => algebraMap O A (a i)) op)
    (Subalgebra.val _) Subtype.val_injective (Subalgebra.range_val _)
  have hCO : Alg.IsCO O (heckeAlg (locPart Y op fun i => algebraMap O A (a i)) op) := by
    refine UpperTheory.V.Alg.co_finite O A _ ?_
    intro x
    obtain ⟨c, hc'⟩ := hres x
    obtain ⟨d, hd⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := O) c
    refine ⟨d, ?_⟩
    have h2 := map_nonunit (algebraMap A (heckeAlg (locPart Y op fun i => algebraMap O A (a i)) op)) _ hd
    rw [IsScalarTower.algebraMap_apply O A _ d]
    have h3 := Ideal.add_mem _ hc' h2
    rw [map_sub, sub_add_sub_cancel] at h3
    exact h3
  refine ⟨hCO, RingHom.finite_algebraMap.2 hfin, ?_, ?_⟩
  · intro b hb t ht
    exact (mem_nonZeroDivisors_iff.1 (hnzd b hb)).1 t ht
  · intro i
    have h5 := hgen i (heckeGen _ op i) (fun y => rfl)
    rw [IsScalarTower.algebraMap_apply O A _ (a i)]
    exact h5

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Hi.hiAlg :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], H.MK θ a K ≠ ⊥ → ∃ _ : Alg.IsCO c.O (H.TK θ a K), (algebraMap A (H.TK θ a K)).Finite ∧ (IsDomain A → ∀ b : A, b ≠ 0 → ∀ t : H.TK θ a K, algebraMap A (H.TK θ a K) b * t = 0 → t = 0) ∧ (∀ i, H.gen θ a K i - algebraMap c.O (H.TK θ a K) (a i) ∈ maximalIdeal (H.TK θ a K)) ∧ (∀ v j, IsUnit (H.gen θ a K (.inr (v, j)))) ∧ Algebra.adjoin A (Set.range (H.gen θ a K)) = ⊤ := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ a K _ hne
  haveI : Finite (IsLocalRing.ResidueField c.O) := by
    haveI := c.fin
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hcY, hfY, hfrY, hMK⟩ := hiComm L Ω l n c H hAx A θ hθ K
  obtain ⟨-, hfM, -⟩ := hMK a
  haveI := hfY
  haveI := hfM
  haveI := hfrY
  have hP : ∀ (v : H.V) (k : ℕ), alV n H.Sl v k ∈ H.X.I.P := by
    intro v k
    unfold UpperTheory.V.Hi.alV UpperTheory.V.Hi.HSet.X
    dsimp only
    unfold UpperTheory.V.Hi.iwS UpperTheory.V.Hi.piIwa
    dsimp only
    unfold UpperTheory.V.Hi.piData
    dsimp only
    intro w _
    by_cases hw : w = v
    · subst hw
      simp only [Pi.mulSingle_eq_same]
      exact al_mem _ n k
    · simp only [Pi.mulSingle, Function.update, hw, dif_neg, not_false_eq_true, Pi.one_apply]
      exact (glIwa _ n).P.one_mem
  obtain ⟨-, -, hbij⟩ := ordFree _ _ _ H.X A H.m (H.τA A) θ hθ.cont (H.lev K) (hAx.fin K) (hθ.free K)
  obtain ⟨hCO, hfin, hnz, hres⟩ := hiAlg_abs (O := c.O) (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) a hcY
    (H.MK θ a K) rfl hne
  refine ⟨hCO, hfin, ?_, hres, ?_, hiAlg_top _ _⟩
  · intro hdom b hb t ht
    refine hnz b ?_ t ht
    intro y hy hby
    have h0 : b • (⟨y, hy⟩ : H.X.Ord (H.τA A) θ (H.lev K)) = 0 := Subtype.ext hby
    rcases smul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hb
    · exact congrArg Subtype.val h1
  · intro v j
    exact hiAlg_unit (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A) (.inr (v, j))
      (hbij _ (hP v (j + 1)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2BaseAct
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2BaseAct :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K : H.Lev) (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R) (J : Ideal R), H.IsJ θ a K D₀ ψ₀ lam J → ∃ μ : R →+* Module.End A (H.MK θ a K), (∀ b y, μ (lam b) y = b • y) ∧ RingHom.ker μ = J ∧ (H.MK θ a K = ⊥ ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K), H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))) := by
  intro L Ω _ _ _ _ _ l _ n c H _ A _ _ _ θ _ a K R _ _ D₀ ψ₀ lam J hJ
  rcases hJ with ⟨h0, hJ⟩ | ⟨x, x1, f, hne, hmap, hsurj, hlam, hker⟩
  · haveI : Subsingleton (H.MK θ a K) := by
      rw [h0]
      infer_instance
    haveI : Subsingleton (Module.End A (H.MK θ a K)) := inferInstance
    let μ : R →+* Module.End A (H.MK θ a K) :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    refine ⟨μ, ?_, ?_, Or.inl h0⟩
    · intro b y
      exact Subsingleton.elim _ _
    · rw [hJ]
      ext t
      simp only [RingHom.mem_ker, Submodule.mem_top, iff_true]
      exact Subsingleton.elim _ _
  · refine ⟨(UpperTheory.V.Hi.heckeAlg (H.MK θ a K) (H.op A)).val.toRingHom.comp f.toRingHom, ?_, ?_, Or.inr ⟨x, x1, f, hmap, fun t => rfl⟩⟩
    · intro b y
      have h := hlam b
      show ((f (lam b) : Module.End A (H.MK θ a K))) y = b • y
      rw [h]
      rfl
    · rw [hker]
      ext t
      simp only [RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      constructor
      · intro ht
        exact Subtype.ext ht
      · intro ht
        rw [ht]
        rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2BasePack
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2BasePack :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (wt : Pa.WtVars (Pa.locOf r) O n D) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] B.B), (∀ k, residue O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField O) = 1) → (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O B.B (wt.c k) * (B.u.ψ (wt.v k) (wt.i k) (wt.γ k) : B.B) - 1) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M] (μ : B.B →+* Module.End A M), (∀ a y, μ (lam a) y = a • y) → RingHom.ker μ = J → ∃ (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (eb : M ≃+ b.M), b.wt = wt ∧ ∀ t y, eb (μ t y) = t • eb y := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D wt A _ _ e lam hres hlam M _ _ _ _ μ hμ hker
  letI mB : Module B.B M := Module.compHom M μ
  letI mL : Module (Pa.abelian₂ O Empty D) M := Module.compHom M (e : Pa.abelian₂ O Empty D →+* A)
  have hsm : ∀ (a : Pa.abelian₂ O Empty D) (m : M), a • m = (lam.comp e.toAlgHom) a • m := by
    intro a m
    exact (hμ (e a) m).symm
  haveI : Nontrivial A := e.injective.nontrivial
  let bL := (Module.Free.chooseBasis A M).mapCoeffs e.symm.toRingEquiv (fun c x => by
    show e (e.symm c) • x = c • x
    rw [AlgEquiv.apply_symm_apply])
  haveI : Module.Free (Pa.abelian₂ O Empty D) M := Module.Free.of_basis bL
  haveI : Module.Finite (Pa.abelian₂ O Empty D) M := Module.Finite.of_basis bL
  have hann : Module.annihilator B.B M = J := by
    rw [← hker]
    ext b
    rw [Module.mem_annihilator, RingHom.mem_ker]
    constructor
    · intro hb
      ext m
      exact hb m
    · intro hb m
      show μ b m = 0
      rw [hb]
      rfl
  exact ⟨Pa.TWBase.mk wt hres (lam.comp e.toAlgHom) (fun k => hlam k) M hsm inferInstance inferInstance
    (fun p _ => by rw [hann]), AddEquiv.refl M, rfl, fun t y => rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2EigPart
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2EigPart :
    ∀ (K W ι : Type) [Field K] [AddCommGroup W] [Module K W] (J : Type 1) (op : ι → Module.End K W) (Z : J → Submodule K W) (μ : J → ι → K), (∀ j i, ∀ F ∈ Z j, op i F = μ j i • F) → ∀ F ∈ ⨆ j, Z j, F ≠ 0 → ∀ ν : ι → K, (∀ i, op i F = ν i • F) → ∃ j, μ j = ν := by
  intro K W ι _ _ _ J op Z μ hZ F hF hF0 ν hν
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hF
  have inv : ∀ (t : Finset J) i, ∀ G ∈ ⨆ j ∈ t, Z j, op i G ∈ ⨆ j ∈ t, Z j := by
    intro t i
    have hle : (⨆ j ∈ t, Z j) ≤ (⨆ j ∈ t, Z j).comap (op i) := by
      refine iSup₂_le fun j hj => ?_
      intro G hG
      rw [Submodule.mem_comap, hZ j i G hG]
      exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun j (_ : j ∈ t) => Z j) j hj) hG)
    exact fun G hG => hle hG
  suffices key : ∀ t : Finset J, ∀ G ∈ ⨆ j ∈ t, Z j, G ≠ 0 → (∀ i, op i G = ν i • G) → ∃ j, μ j = ν from
    key s F hs hF0 hν
  intro t
  refine Finset.induction_on t ?_ ?_
  · intro G hG hG0 _
    simp at hG
    exact absurd hG hG0
  · intro a t ha ih G hG hG0 hGν
    rw [Finset.iSup_insert, Submodule.mem_sup] at hG
    obtain ⟨H, hH, G', hG', rfl⟩ := hG
    by_cases hμ : μ a = ν
    · exact ⟨a, hμ⟩
    obtain ⟨i, hi⟩ : ∃ i, μ a i ≠ ν i := by
      by_contra h
      push_neg at h
      exact hμ (funext h)
    have e : (μ a i - ν i) • H = ν i • G' - op i G' := by
      have h1 := hGν i
      rw [map_add (f := _), hZ a i H hH, smul_add] at h1
      rw [sub_smul, sub_eq_sub_iff_add_eq_add, h1, add_comm]
    have hsub : (μ a i - ν i) • H ∈ ⨆ j ∈ t, Z j := by
      rw [e]
      exact sub_mem (Submodule.smul_mem _ _ hG') (inv t i G' hG')
    have hH' : H ∈ ⨆ j ∈ t, Z j := by
      have hne : μ a i - ν i ≠ 0 := sub_ne_zero.mpr hi
      have h2 := Submodule.smul_mem _ (μ a i - ν i)⁻¹ hsub
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    exact ih (H + G') (add_mem hH' hG') hG0 hGν
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Glue
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2Glue :
    ∀ (A R P κ : Type) [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Nonempty κ] (N : κ → Submodule A P) (μ : ∀ k, R →+* Module.End A (N k)), (∀ z, ∃ k, z ∈ N k) → (∀ k k', ∃ k'', N k ≤ N k'' ∧ N k' ≤ N k'') → (∀ k k' (h : N k ≤ N k') t (y : N k), ((μ k' t (Submodule.inclusion h y) : N k') : P) = (μ k t y : N k)) → ∃ α : R →+* Module.End A P, ∀ k t (y : N k), α t y = (μ k t y : N k) := by
  intro A R P κ _ _ _ _ _ N μ hcov hdir hcomp
  have key : ∀ t (z : P) k k' (hk : z ∈ N k) (hk' : z ∈ N k'),
      ((μ k t ⟨z, hk⟩ : N k) : P) = ((μ k' t ⟨z, hk'⟩ : N k') : P) := by
    intro t z k k' hk hk'
    obtain ⟨k'', h1, h2⟩ := hdir k k'
    have e1 := hcomp k k'' h1 t ⟨z, hk⟩
    have e2 := hcomp k' k'' h2 t ⟨z, hk'⟩
    have e3 : Submodule.inclusion h1 ⟨z, hk⟩ = Submodule.inclusion h2 ⟨z, hk'⟩ := Subtype.ext rfl
    rw [← e1, ← e2, e3]
  let f : R → P → P := fun t z => ((μ (hcov z).choose t ⟨z, (hcov z).choose_spec⟩ : N _) : P)
  have hf : ∀ t k (y : N k), f t y = ((μ k t y : N k) : P) := fun t k y => key t y _ k _ y.2
  have two : ∀ z w : P, ∃ k, z ∈ N k ∧ w ∈ N k := by
    intro z w
    obtain ⟨k1, h1⟩ := hcov z
    obtain ⟨k2, h2⟩ := hcov w
    obtain ⟨k, hk1, hk2⟩ := hdir k1 k2
    exact ⟨k, hk1 h1, hk2 h2⟩
  let L : R → Module.End A P := fun t =>
    { toFun := f t
      map_add' := by
        intro z w
        obtain ⟨k, hz, hw⟩ := two z w
        calc f t (z + w) = f t ((⟨z, hz⟩ + ⟨w, hw⟩ : N k) : P) := rfl
          _ = ((μ k t (⟨z, hz⟩ + ⟨w, hw⟩) : N k) : P) := hf t k _
          _ = ((μ k t ⟨z, hz⟩ : N k) : P) + ((μ k t ⟨w, hw⟩ : N k) : P) := by
            rw [map_add (f := _), Submodule.coe_add]
          _ = f t z + f t w := by rw [← hf t k ⟨z, hz⟩, ← hf t k ⟨w, hw⟩]
      map_smul' := by
        intro a z
        obtain ⟨k, hz⟩ := hcov z
        calc f t (a • z) = f t ((a • ⟨z, hz⟩ : N k) : P) := rfl
          _ = ((μ k t (a • ⟨z, hz⟩) : N k) : P) := hf t k _
          _ = a • ((μ k t ⟨z, hz⟩ : N k) : P) := by rw [map_smul, Submodule.coe_smul]
          _ = (RingHom.id A) a • f t z := by rw [RingHom.id_apply, ← hf t k ⟨z, hz⟩] }
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f 1 z = z
    exact (hf 1 k ⟨z, hz⟩).trans (by simp)
  · intro s t
    refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f (s * t) z = f s (f t z)
    calc f (s * t) z = ((μ k (s * t) ⟨z, hz⟩ : N k) : P) := hf _ k ⟨z, hz⟩
      _ = ((μ k s (μ k t ⟨z, hz⟩) : N k) : P) := by rw [map_mul]; rfl
      _ = f s ((μ k t ⟨z, hz⟩ : N k) : P) := (hf s k _).symm
      _ = f s (f t z) := congrArg (f s) (hf t k ⟨z, hz⟩).symm
  · refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f 0 z = 0
    exact (hf 0 k ⟨z, hz⟩).trans (by simp)
  · intro s t
    refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f (s + t) z = f s z + f t z
    calc f (s + t) z = ((μ k (s + t) ⟨z, hz⟩ : N k) : P) := hf _ k ⟨z, hz⟩
      _ = ((μ k s ⟨z, hz⟩ : N k) : P) + ((μ k t ⟨z, hz⟩ : N k) : P) := by
        rw [map_add (f := _), LinearMap.add_apply, Submodule.coe_add]
      _ = f s z + f t z := by rw [← hf s k ⟨z, hz⟩, ← hf t k ⟨z, hz⟩]
  · intro k t y
    exact hf t k y
end

