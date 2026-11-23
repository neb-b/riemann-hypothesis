module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.DcMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.FinFam
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem comp_of_proj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {π σ : Submodule ℂ (UA L n → ℂ)} (hπ : IsAutRepU π)
    (P : GlobalTheory.DefU.autU L n →ₗ[ℂ] GlobalTheory.DefU.autU L n) (hP : ∀ φ, (P φ).1 ∈ σ)
    (he : ∀ x φ, P (GlobalTheory.DefU.autRep L n x φ) = GlobalTheory.DefU.autRep L n x (P φ))
    (ψ : GlobalTheory.DefU.autU L n) (hψ : ψ.1 ∈ π) (h0 : P ψ ≠ 0) (w : Plc L) (τ : SmIrr (GL (Fin n) (Kw w)))
    (h : Comp π w τ) : Comp σ w τ := by
  have hle : π ≤ GlobalTheory.DefU.autU L n := hπ.aut
  have hK : π ⊓ (LinearMap.ker P).map (GlobalTheory.DefU.autU L n).subtype = ⊥ := by
    refine (hπ.irred _ inf_le_left ?_).resolve_right fun e => h0 ?_
    · rintro x _ ⟨h1, φ, h2, rfl⟩
      refine ⟨hπ.stable x _ h1, GlobalTheory.DefU.autRep L n x φ, ?_, rfl⟩
      have h2' : P φ = 0 := h2
      change P _ = 0
      rw [he, h2', map_zero]
    · obtain ⟨-, φ, h2, h3⟩ := e.ge hψ
      obtain rfl : φ = ψ := Subtype.ext h3
      exact h2
  obtain ⟨h1, f, hf0, hf, h2⟩ := h
  let g := f.codRestrict (GlobalTheory.DefU.autU L n) fun v => hle (hf v)
  refine ⟨h1, (GlobalTheory.DefU.autU L n).subtype ∘ₗ P ∘ₗ g, fun e => hf0 (LinearMap.ext fun v => ?_), fun v => hP _,
    fun x v => ?_⟩
  · have h3 : P (g v) = 0 := Subtype.ext (LinearMap.congr_fun e v)
    exact hK.le ⟨hf v, g v, h3, rfl⟩
  · have h3 : g (τ.ρ (((cLoc w).comp (locU n w).subtype) x) v) = GlobalTheory.DefU.autRep L n x (g v) :=
      Subtype.ext (h2 x v)
    exact congrArg Subtype.val ((congrArg P h3).trans (he x _))

theorem UpperTheory.V.Z.Sym.Al.finFam :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U →
        ∃ A : Set (Submodule ℂ (UA L n → ℂ)), A.Finite ∧ (∀ σ ∈ A, IsAutRepU σ) ∧
          ∀ π, IsAutRepU π → ∀ φ : UA L n → V, φ ≠ 0 → IsAF R U φ → CoefIn φ π → ∃ σ ∈ A, ∀ w τ, Comp π w τ → Comp σ w τ := by
  intro L _ _ _ n V _ _ _ R hR U hU
  have := afFin L n V R U hU
  let b := Module.finBasis ℂ V
  let T : Fin (Module.finrank ℂ V) → AF R U →ₗ[ℂ] GlobalTheory.DefU.autU L n := fun i =>
    (((b.coord i).compLeft (UA L n)) ∘ₗ (AF R U).subtype).codRestrict _ fun φ =>
      coefAut L n V R hR U hU φ.1 φ.2 (b.coord i)
  obtain ⟨κ, _, σ, P, h1, h2, h3, h4⟩ := autProj L n (⨆ i, LinearMap.range (T i)) inferInstance
  refine ⟨Set.range σ, Set.finite_range σ, ?_, fun π hπ φ h0 hφ hc => ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact h1 i
  obtain ⟨i, hi⟩ : ∃ i, T i ⟨φ, hφ⟩ ≠ 0 := by
    by_contra! h
    refine h0 (funext fun g => b.ext_elem fun i => ?_)
    have h5 : b.coord i (φ g) = 0 := congrFun (congrArg Subtype.val (h i)) g
    simpa using h5
  obtain ⟨k, hk⟩ : ∃ k, P k (T i ⟨φ, hφ⟩) ≠ 0 := by
    by_contra! h
    refine hi ?_
    rw [← h4 (T i ⟨φ, hφ⟩) (Submodule.mem_iSup_of_mem i ⟨_, rfl⟩)]
    simp [h]
  exact ⟨σ k, ⟨k, rfl⟩, comp_of_proj hπ (P k) (h2 k) (h3 k) _ (hc (b.coord i)) hk⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Imports
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.proj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U → ∀ φ : UA L n → V, φ ≠ 0 → IsAF R U φ →
        ∃ (σ : Submodule ℂ (UA L n → ℂ)) (φ' : UA L n → V), IsAutRepU σ ∧ φ' ≠ 0 ∧ IsAF R U φ' ∧ CoefIn φ' σ ∧
          ∀ w W d c, EigAt φ w W d c → EigAt φ' w W d c := by
  classical
  intro L _ _ _ n V _ _ _ R hR U hU φ hφ hAF
  let C : (V →ₗ[ℂ] ℂ) →ₗ[ℂ] GlobalTheory.DefU.autU L n :=
    { toFun := fun f => ⟨f ∘ φ, coefAut L n V R hR U hU φ hAF f⟩
      map_add' := fun f f' => Subtype.ext rfl
      map_smul' := fun c f => Subtype.ext rfl }
  obtain ⟨κ, _, σ, P, hσ, hPσ, hPe, hPs⟩ := autProj L n (LinearMap.range C) inferInstance
  let b := Module.finBasis ℂ V
  let F : κ → UA L n → V := fun k g => ∑ i, (P k (C (b.coord i))).1 g • b i
  have hF : ∀ k (f : V →ₗ[ℂ] ℂ) g, f (F k g) = (P k (C f)).1 g := by
    intro k f g
    conv_rhs => rw [← b.sum_dual_apply_smul_coord f]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sum, map_smul, smul_eq_mul, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul, Pi.smul_apply, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hext : ∀ {v v' : V}, (∀ f : V →ₗ[ℂ] ℂ, f v = f v') → v = v' := fun h =>
    b.ext_elem fun i => h (b.coord i)
  have hsum : ∀ f, ∑ k, P k (C f) = C f := fun f => hPs _ ⟨f, rfl⟩
  have hne : ∃ k, F k ≠ 0 := by
    by_contra h
    push_neg at h
    refine hφ (funext fun g => hext fun f => ?_)
    have e := congrArg (fun x : GlobalTheory.DefU.autU L n => x.1 g) (hsum f)
    simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply] at e
    have e' : (C f).1 g = f (φ g) := rfl
    rw [Pi.zero_apply, map_zero, ← e', ← e]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← hF, h k]
    simp
  obtain ⟨k, hk⟩ := hne
  have htr : ∀ x (f : V →ₗ[ℂ] ℂ) g, (P k (C f)).1 (g * x) = (P k (GlobalTheory.DefU.autRep L n x (C f))).1 g := by
    intro x f g
    rw [hPe]
    rfl
  have hcoef : ∀ f : V →ₗ[ℂ] ℂ, f ∘ F k = (P k (C f)).1 := fun f => funext (hF k f)
  refine ⟨σ k, F k, hσ k, hk, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact fun γ hγ g => hext fun f => by
      rw [hF, hF]
      exact (P k (C f)).2.left γ hγ g
  · refine fun x hx g => hext fun f => ?_
    have e : GlobalTheory.DefU.autRep L n x (C f) = C (f ∘ₗ R (infC L n x⁻¹)) :=
      Subtype.ext (funext fun g => by
        change f (φ (g * x)) = f (R _ (φ g))
        rw [hAF.inf x hx])
    rw [hF, htr, e, ← hF]
    rfl
  · refine fun u hu g => hext fun f => ?_
    have e : GlobalTheory.DefU.autRep L n u (C f) = C f :=
      Subtype.ext (funext fun g => by
        change f (φ (g * u)) = f (φ g)
        rw [hAF.level u hu])
    rw [hF, hF, htr, e]
  · intro f
    rw [hcoef]
    exact hPσ k _
  · intro w W d c h
    let ρV := (rightReg ℂ (UA L n) V).comp (secW n w)
    let ρC := (rightReg ℂ (UA L n) ℂ).comp (secW n w)
    let ρA := (GlobalTheory.DefU.autRep L n).comp (secW n w)
    have e1 : ∀ (f : V →ₗ[ℂ] ℂ) (ψ : UA L n → V) a,
        f ∘ (Hi.dc ρV (W.J n) (W.J n) a ψ) = Hi.dc ρC (W.J n) (W.J n) a (f ∘ ψ) := fun f ψ a =>
      dcMap W ρV ρC (f.compLeft (UA L n)) (fun _ _ => rfl) a ψ
    have e2 : ∀ (x : GlobalTheory.DefU.autU L n) a,
        (Hi.dc ρA (W.J n) (W.J n) a x).1 = Hi.dc ρC (W.J n) (W.J n) a x.1 := fun x a =>
      dcMap W ρA ρC (GlobalTheory.DefU.autU L n).subtype (fun _ _ => rfl) a x
    have e3 : ∀ (x : GlobalTheory.DefU.autU L n) a,
        P k (Hi.dc ρA (W.J n) (W.J n) a x) = Hi.dc ρA (W.J n) (W.J n) a (P k x) := fun x a =>
      dcMap W ρA ρA (P k) (fun _ _ => hPe k _ _) a x
    change Hi.dc ρV (W.J n) (W.J n) (Sig.dg d) φ = c • φ at h
    change Hi.dc ρV (W.J n) (W.J n) (Sig.dg d) (F k) = c • F k
    refine funext fun g => hext fun f => ?_
    have hC : Hi.dc ρA (W.J n) (W.J n) (Sig.dg d) (C f) = c • C f := Subtype.ext (by
      rw [e2]
      change Hi.dc ρC (W.J n) (W.J n) (Sig.dg d) (f ∘ φ) = c • (f ∘ φ)
      rw [← e1, h]
      funext g
      simp)
    have e4 : f ∘ (Hi.dc ρV (W.J n) (W.J n) (Sig.dg d) (F k)) =
        (Hi.dc ρA (W.J n) (W.J n) (Sig.dg d) (P k (C f))).1 := by
      rw [e1, e2, hcoef]
    have e5 := congrFun e4 g
    rw [← e3, hC, map_smul] at e5
    simp only [Function.comp_apply] at e5
    rw [e5]
    simp [hF]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanSph
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al.SphericalSpanAlt

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private noncomputable def intPts (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Subgroup (finU (E := L) (n := n)) :=
  (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL L n).comap (GlobalTheory.BCT.GlobLev.finPart L n)

private theorem isOpen_intPts : IsOpen (intPts L n : Set (finU (E := L) (n := n))) :=
  (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL L n).preimage GlobalTheory.BCT.GlobLev.continuous_finPart

private theorem isCompact_intPts : IsCompact (intPts L n : Set (finU (E := L) (n := n))) := by
  refine IsCompact.of_isClosed_subset (GlobalTheory.BCT.GlobLev.isClosedEmbedding_finU.isCompact_preimage
    ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL L n).image GlobalTheory.BCT.GlobLev.continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ isOpen_intPts) fun x hx => ⟨GlobalTheory.BCT.GlobLev.finPart L n x, hx, ?_⟩
  have h1 : Matrix.GeneralLinearGroup.map (pInf L) ((x : UA L n) : GA L n) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

private theorem mem_intPts {k : finU (E := L) (n := n)} (h : ∀ u, cLoc u (k : UA L n) ∈ GlobalTheory.LFun.KGL u (n := n)) : k ∈ intPts L n := by
  rw [intPts, Subgroup.mem_comap, GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles] at h ⊢
  exact ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩

end UpperTheory.V.Z.Sym.Al.SphericalSpanAlt

namespace UpperTheory.V.Z.Sym.Al.SphericalSpanAlt

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem finite_quot (w : Plc L) (U : Subgroup (UA L n))
    (hU : IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U}) :
    Finite ((locU n w ⊓ Kall L n : Subgroup (UA L n)) ⧸ U.subgroupOf (locU n w ⊓ Kall L n)) := by
  haveI : CompactSpace (intPts L n) := isCompact_iff_compactSpace.1 isCompact_intPts
  let U' : Subgroup (finU (E := L) (n := n)) := U.subgroupOf (finU (E := L) (n := n))
  have hU' : IsOpen (U' : Set (finU (E := L) (n := n))) := hU
  let H : Subgroup (intPts L n) := U'.subgroupOf (intPts L n)
  have hH : IsOpen (H : Set (intPts L n)) := hU'.preimage continuous_subtype_val
  haveI : Finite (intPts L n ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hfin : ∀ k : (locU n w ⊓ Kall L n : Subgroup (UA L n)), (k : UA L n) ∈ finU (E := L) (n := n) := fun k =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 k.2).2).1
  have hint : ∀ (k : (locU n w ⊓ Kall L n : Subgroup (UA L n))) (u : Plc L),
      cLoc u (k : UA L n) ∈ GlobalTheory.LFun.KGL u (n := n) := fun k u =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 k.2).2).2 u)
  let f : (locU n w ⊓ Kall L n : Subgroup (UA L n)) →* intPts L n :=
    { toFun := fun k => ⟨⟨k.1, hfin k⟩, mem_intPts (hint k)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have e : U.subgroupOf (locU n w ⊓ Kall L n) = H.comap f := by
    ext k
    rfl
  rw [e]
  refine Finite.of_injective (fun q : _ ⧸ H.comap f => ((f (Quotient.out q) : intPts L n) : intPts L n ⧸ H))
    fun q q' e' => ?_
  have e'' := QuotientGroup.eq.1 e'
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  refine QuotientGroup.eq.2 ?_
  show f (_ * _) ∈ H
  rw [map_mul, map_inv]
  exact e''

private theorem sum_translate {G X : Type} [Group G] [AddCommMonoid X] (K : Subgroup G) (K' : Subgroup K)
    [Fintype (K ⧸ K')] (F : G → X) (hF : ∀ t, ∀ m ∈ K', F (t * ((m : K) : G)) = F t) (k : G) (hk : k ∈ K) (t : G) :
    ∑ q : K ⧸ K', F (t * k * ((Quotient.out q : K) : G)) = ∑ q : K ⧸ K', F (t * ((Quotient.out q : K) : G)) := by
  let kk : K := ⟨k, hk⟩
  have step : ∀ q : K ⧸ K', F (t * k * ((Quotient.out q : K) : G)) =
      F (t * ((Quotient.out (kk • q) : K) : G)) := by
    intro q
    have hm : (Quotient.out (kk • q))⁻¹ * (kk * Quotient.out q) ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [← hF (t * ((Quotient.out (kk • q) : K) : G)) _ hm]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, kk, mul_assoc, mul_inv_cancel_left]
  rw [Finset.sum_congr rfl fun q _ => step q]
  exact Fintype.sum_equiv (MulAction.toPerm kk) _ _ fun q => rfl

end UpperTheory.V.Z.Sym.Al.SphericalSpanAlt

open UpperTheory.V.Z.Sym.Al.SphericalSpanAlt in
theorem UpperTheory.V.Z.Sym.Al.spanSph :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ w : Plc L, IsUnramU π w →
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π → ∃ φ', φ' ≠ 0 ∧ InSpan w φ φ' ∧ ∀ x ∈ locU n w ⊓ Kall L n, ∀ g, φ' (g * x) = φ' g := by
  classical
  intro L _ _ _ n V _ _ _ π hπ w hw φ h0 hc
  obtain ⟨f1, f2, -, -, f5, -⟩ := factor L n w
  obtain ⟨ψ, hψ, hψ0, hψK⟩ := hw
  obtain ⟨g0, hg0⟩ := Function.ne_iff.1 h0
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℂ] ℂ, f (φ g0) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)
  have hhπ : f ∘ φ ∈ π := hc f
  have hh0 : f ∘ φ ≠ 0 := fun e => hf (congrFun e g0)
  have rmul : ∀ (a b : UA L n) (F : UA L n → ℂ), RU L n (a * b) F = RU L n a (RU L n b F) :=
    fun a b F => by rw [map_mul]; rfl

  let S := Submodule.span ℂ (Set.range fun g : UA L n => RU L n g (f ∘ φ))
  have hSπ : S ≤ π := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hπ.stable g _ hhπ)
  have hSst : ∀ a, ∀ F ∈ S, RU L n a F ∈ S := by
    intro a F hF
    have hle : S ≤ S.comap (RU L n a) := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      show RU L n a (RU L n g (f ∘ φ)) ∈ S
      rw [← rmul]
      exact Submodule.subset_span ⟨_, rfl⟩)
    exact hle hF
  have hhS : f ∘ φ ∈ S := by
    have h1 : RU L n 1 (f ∘ φ) = f ∘ φ := by rw [map_one]; rfl
    rw [← h1]
    exact Submodule.subset_span ⟨1, rfl⟩
  have hSeq : S = π := by
    rcases hπ.irred S hSπ hSst with e | e
    · exact absurd ((Submodule.mem_bot ℂ).1 (e ▸ hhS)) hh0
    · exact e
  obtain ⟨c, hcs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hSeq ▸ hψ : ψ ∈ S)

  choose x hx y hy hxy using f2
  let φg : UA L n → UA L n → V := fun g t => φ (t * x g)
  have hcoef : ∀ g, CoefIn (φg g) π := fun g f' => hπ.stable (x g) _ (hc f')
  choose U hUo hUf using fun g => openLev L n V π hπ (φg g) (hcoef g)
  let U0 : Subgroup (UA L n) := ⨅ g ∈ c.support, U g
  have hU0 : IsOpen {k : finU (E := L) (n := n) | (k : UA L n) ∈ U0} := by
    have e : {k : finU (E := L) (n := n) | (k : UA L n) ∈ U0} = ⋂ g ∈ c.support, {k : finU (E := L) (n := n) | (k : UA L n) ∈ U g} := by
      ext k
      simp only [U0, Subgroup.mem_iInf, Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact isOpen_biInter_finset fun g _ => hUo g
  let K : Subgroup (UA L n) := locU n w ⊓ Kall L n
  let K' : Subgroup K := U0.subgroupOf K
  haveI : Finite (K ⧸ K') := finite_quot w U0 hU0
  letI : Fintype (K ⧸ K') := Fintype.ofFinite _
  let rep : K ⧸ K' → UA L n := fun q => ((Quotient.out q : K) : UA L n)
  have hrepK : ∀ q, rep q ∈ K := fun q => (Quotient.out q).2
  have hrepl : ∀ q, rep q ∈ locU n w := fun q => (Subgroup.mem_inf.1 (hrepK q)).1
  let A : UA L n → UA L n → V := fun g t => ∑ q, φg g (t * rep q)
  have hψfix : ∀ k ∈ K, ∀ t, ψ (t * k) = ψ t := fun k hk t => by
    obtain ⟨k1, k2⟩ := Subgroup.mem_inf.1 hk
    exact congrFun (hψK k k1 ((f5 k k1).1 k2)) t
  have hψsum : ∀ s, ψ s = ∑ g ∈ c.support, c g * f (φ (s * g)) := by
    intro s
    rw [← hcs, Finsupp.sum, Finset.sum_apply]
    rfl
  have key : ∀ t, (Fintype.card (K ⧸ K') : ℂ) * ψ t = ∑ g ∈ c.support, c g * f (A g (t * y g)) := by
    intro t
    have e1 : (Fintype.card (K ⧸ K') : ℂ) * ψ t = ∑ q : K ⧸ K', ψ (t * rep q) := by
      rw [Finset.sum_congr rfl fun q _ => hψfix _ (hrepK q) t, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    rw [e1, Finset.sum_congr rfl fun q _ => hψsum _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.mul_sum, map_sum]
    refine congrArg (c g * ·) (Finset.sum_congr rfl fun q _ => ?_)
    have hm : (rep q * x g) * y g = y g * (rep q * x g) :=
      f1 _ ((locU n w).mul_mem (hrepl q) (hx g)) _ (hy g)
    show f (φ (t * rep q * g)) = f (φ (t * y g * rep q * x g))
    congr 2
    calc t * rep q * g = t * ((rep q * x g) * y g) := by
          conv_lhs => rw [hxy g]
          simp only [mul_assoc]
      _ = t * y g * rep q * x g := by rw [hm]; simp only [mul_assoc]
  by_cases hall : ∀ g ∈ c.support, A g = 0
  · exfalso
    have hcard : (Fintype.card (K ⧸ K') : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨(QuotientGroup.mk 1 : K ⧸ K')⟩).ne'
    refine hψ0 (funext fun t => ?_)
    have h := key t
    rw [Finset.sum_eq_zero fun g hg => by rw [hall g hg]; simp] at h
    exact (mul_eq_zero.1 h).resolve_left hcard
  · push_neg at hall
    obtain ⟨g, hg, hne⟩ := hall
    refine ⟨A g, hne, ?_, ?_⟩
    · have e : A g = ∑ q : K ⧸ K', fun t => φ (t * (rep q * x g)) := by
        funext t
        simp only [A, φg, Finset.sum_apply, mul_assoc]
      unfold InSpan
      rw [e]
      exact Submodule.sum_mem _ fun q _ =>
        Submodule.subset_span ⟨_, (locU n w).mul_mem (hrepl q) (hx g), rfl⟩
    · intro k hk t
      exact sum_translate K K' (φg g) (fun s m hm => hUf g _ (Subgroup.mem_iInf.1
        (Subgroup.mem_iInf.1 (Subgroup.mem_subgroupOf.1 hm) g) hg) s) k hk t
end

