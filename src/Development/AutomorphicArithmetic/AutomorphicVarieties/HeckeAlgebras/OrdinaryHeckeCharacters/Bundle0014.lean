module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AutomorphicTensorInductionOfLocalPlaces
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem neu_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L} {j : GLw n w →* UA L n}
    (hj : ∀ x ∈ locU n w, x = j (cLoc w x)) {g y : UA L n} (hg : cLoc w g = 1) (hy : y ∈ locU n w) : Commute g y := by
  have h1 : (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = 1 := by
    rw [hj _ (GlobalTheory.DefU.LocRet.ret w n g).2]
    have : cLoc w (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = cLoc w g := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl g
    rw [this, hg, map_one]
  have h2 := GlobalTheory.DefU.LocRet.commute_ret g ⟨y, hy⟩
  rwa [h1, inv_one, one_mul] at h2

private theorem ne_J {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {St : Type} [Fintype St] [DecidableEq St]
    {wt : St → Plc L} (hinj : Function.Injective fun u => (wt u).under (𝓞 (Lp L))) (j : ∀ u, GLw n (wt u) →* UA L n)
    (h1 : ∀ u g, j u g ∈ locU n (wt u)) (h2 : ∀ u g, cLoc (wt u) (j u g) = g) (h3 : ∀ u, ∀ x ∈ locU n (wt u), x = j u (cLoc (wt u) x)) :
    ∃ J : GV n wt →* UA L n, (∀ u g, J (Pi.mulSingle u g) = j u g) ∧ (∀ g, J g ∈ GlobalTheory.UnitaryBC.finU (E := L) (n := n)) ∧
      (∀ g u, cLoc (wt u) (J g) = g u) ∧
      (∀ g (v : Plc L), (∀ u, v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L))) → cLoc v (J g) = 1) ∧
      ∀ g k, (∀ u, cLoc (wt u) k = 1) → Commute k (J g) := by
  have h4 : ∀ u g (v : Plc L), v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L)) → cLoc v (j u g) = 1 := fun u g v hv =>
    GlobalTheory.DefU.LocRet.mem_locU_ne (h1 u g) hv
  have hc : Pairwise fun a b => ∀ x y, Commute (j a x) (j b y) := fun a b hab x y =>
    neu_comm (h3 b) (h4 a x _ fun e => hab (hinj e).symm) (h1 b y)
  let J := MonoidHom.noncommPiCoprod j hc
  have hJ : ∀ u g, J (Pi.mulSingle u g) = j u g := fun u g => MonoidHom.noncommPiCoprod_mulSingle j u g
  have key : ∀ P : Subgroup (UA L n), (∀ u g, j u g ∈ P) → ∀ g, J g ∈ P := fun P hP g => by
    have : J.range ≤ P := by
      rw [MonoidHom.noncommPiCoprod_range]
      exact iSup_le fun u => by rintro _ ⟨g, rfl⟩; exact hP u g
    exact this ⟨g, rfl⟩
  refine ⟨J, hJ, key _ fun u g => (h1 u g).1, fun g u => ?_, fun g v hv => key (cLoc v).ker (fun u g => h4 u g v (hv u)) g,
    fun g k hk => ?_⟩
  · have : (cLoc (wt u)).comp J = Pi.evalMonoidHom (fun u => GLw n (wt u)) u := MonoidHom.pi_ext fun i x => by
      rw [MonoidHom.comp_apply, hJ, Pi.evalMonoidHom_apply]
      by_cases h : u = i
      · subst h
        rw [h2, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]
        exact h4 i x _ fun e => h (hinj e)
    exact DFunLike.congr_fun this g
  · exact (Subgroup.mem_centralizer_singleton_iff.1
      (key (Subgroup.centralizer {k}) (fun u g => Subgroup.mem_centralizer_singleton_iff.2
        (neu_comm (h3 u) (hk u) (h1 u g)).symm.eq) g)).symm

private theorem automorphic_tensor_induction_of_local_places {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n m : ℕ}
    {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
    (j : ∀ u, GLw n (wt u) →* UA L n) (J : GV n wt →* UA L n)
    (hJ : ∀ u g, J (by classical exact MonoidHom.mulSingle (fun u => GLw n (wt u)) u g) = j u g)
    (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) (hT : IsType ht τ₀ χ)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (τ : ∀ u, SmIrr (GLw n (wt u)))
    (hτ : ∀ u, IsoSum ((RU L n).comp (j u)) σ (τ u)) (F : Fin m → UA L n → ℂ) (hF0 : F ≠ 0) (hF1 : ∀ i, F i ∈ σ)
    (hF2 : ∀ (k : KT n wt) i, ∑ a, τ₀ k i a • RU L n (J k) (F a) = F i) :
    ∀ u rc, IsRec (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (τ u))) := by
  haveI : Nontrivial σ := Submodule.nontrivial_iff_ne_bot.2 hσ.ne_bot
  let ρ : Representation ℂ (GV n wt) σ :=
    (⟨σ, fun g v hv => hσ.stable (J g) v hv⟩ : Subrepresentation ((RU L n).comp J)).toRepresentation
  have hρ : ∀ g (y : σ), (ρ g y : UA L n → ℂ) = RU L n (J g) y := fun _ _ => rfl
  refine (hT.2 σ ρ τ fun u => ?_).1 ⟨fun i => ⟨F i, hF1 i⟩, fun h => hF0 (funext fun i => congrArg Subtype.val (congrFun h i)),
    fun k i => Subtype.ext ?_⟩
  · refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ _ ⊤ σ (τ u) Unit (fun _ => σ.subtype) (hτ u) (fun _ _ _ => Submodule.mem_top)
      (fun _ y _ => y.2) (fun _ g y _ => ?_) fun y _ h => Subtype.ext (h ())
    exact (hρ _ y).trans (by rw [hJ]; rfl)
  · change σ.subtype (∑ a, τ₀ k i a • ρ k ⟨F a, hF1 a⟩) = F i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hF2 k i]
    rfl

theorem UpperTheory.V.Hi.partUR2Type :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, IsType (fun u : s.St => s.hw u) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ →
    ∀ τ : ∀ u : s.St, SmIrr (GLw n (s.w u)), (∀ u : s.St, IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) (τ u).ρ) → ∀ (u : s.St) rc, IsRec (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (τ u))) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ he σ hσ hY χ hT τ hτ
  letI : DecidableEq s.St := fun a b => Classical.propDecidable _
  obtain ⟨hw, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  choose j h1 h2 _ h3 using fun u : s.St => (secU l L Ω s n hn (wt s u) (hsp _ (by
    rw [hw]
    exact s.split _ (Or.inr (Or.inl u.2))))).1
  obtain ⟨J, hJ, j1, j2, j3, -⟩ := ne_J (wt := wt s)
    (fun a b hab => Subtype.ext ((hw _).symm.trans (hab.trans (hw _)))) j h1 h2 h3
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hFσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have f1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ he _ fun _ => rfl).1
  have hex : ∃ i ℓ, toForm ι e (F i) ℓ ≠ 0 := by
    by_contra h
    exact hF0 (funext fun i => f1 (F i) (hB.1 i trivial) fun ℓ => by
      by_contra h'
      exact h ⟨i, ℓ, h'⟩)
  obtain ⟨i₀, ℓ, hℓ⟩ := hex
  have j4 : ∀ g (v : Plc L), v.under (𝓞 (Lp L)) ∉ s.St → cLoc v (J g) = 1 := fun g v hv =>
    j3 g v fun a h => hv (by rw [h, hw]; exact a.2)
  refine automorphic_tensor_induction_of_local_places (fun u : s.St => s.hw u) j J (fun u g => ?_) _ χ hT hσ τ
    (fun u => UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ (j u) (h1 u) (h2 u) (h3 u) (τ u) (hτ u)) (fun i => toForm ι e (F i) ℓ)
    (fun h => hℓ (congrFun h i₀)) (fun i => hFσ i ℓ) fun k i => ?_
  · exact hJ u g
  · refine partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ he F hB (J k) (j1 _) (fun v => j4 _ _ ?_) k (fun u => (j2 _ u).symm) ?_
      (fun w hw' => ?_) (fun q => j4 _ _ fun h => Q.notS q (Or.inr (Or.inl h))) i ℓ
    · rw [hw]
      exact fun h => s.St_l _ h v.2
    · rw [j4 _ _ (by rw [hw]; exact s.v0_St)]
      exact one_mem _
    · rw [j4 _ _ fun h => hw' (V.sub (Or.inr (Or.inl h)))]
      exact one_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreSep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem coreSep_coord {A M N κ : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module ℂ N]
    (Y : Submodule A M) (φ : A →+* ℂ) (sp : M → N) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = φ b • sp f) (b : Module.Basis κ A Y)
    (hind : LinearIndependent ℂ fun i => sp (b i)) (g : Y) (hg : sp g = 0) (i : κ) : φ (b.repr g i) = 0 := by
  classical
  let s : Y →ₛₗ[φ] N :=
    { toFun := fun f => sp f
      map_add' := fun f f' => hadd _ f.2 _ f'.2
      map_smul' := fun r f => hsmul _ f.2 r }
  have h1 : s g = ∑ j ∈ (b.repr g).support, φ (b.repr g j) • sp (b j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.linearCombination_repr g, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => s.map_smulₛₗ _ _
  by_cases hi : i ∈ (b.repr g).support
  · exact linearIndependent_iff'.1 hind _ (fun j => φ (b.repr g j)) (h1.symm.trans hg) i hi
  · rw [Finsupp.notMem_support_iff.1 hi, map_zero]

private theorem coreSep_kill {N J : Type*} [AddCommGroup N] [Module ℂ N] (E : Submodule ℂ N) (Y : J → Submodule ℂ N)
    (hE : E = ⨆ j, Y j ⊓ E) (T : Module.End ℂ E) (h : ∀ j, ∀ F : E, (F : N) ∈ Y j → T F = 0) (F : E) : T F = 0 := by
  have hle : E ≤ (LinearMap.ker T).map E.subtype := by
    conv_lhs => rw [hE]
    exact iSup_le fun j G hG => ⟨⟨G, hG.2⟩, h j ⟨G, hG.2⟩ hG.1, rfl⟩
  obtain ⟨G, hG, hGF⟩ := hle F.2
  have : G = F := Subtype.ext hGF
  exact this ▸ hG

theorem UpperTheory.V.Hi.coreSep :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], ∀ lam ∈ H.admitted, H.DenseWt θ lam → ∀ t : H.TK θ a K, (∀ x : H.TK θ a K →ₐ[c.O] Qbar l, H.Good θ (x.toRingHom.comp (algebraMap A _)) lam → x t = 0) → t = 0 := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ ι P hP a K _ lam hlam hD t ht
  obtain ⟨-, -, hfree, -⟩ := hiComm L Ω l n c H hAx A θ hθ K
  let b := Module.Free.chooseBasis A (H.X.Ord (H.τA A) θ (H.lev K))
  refine Subtype.ext (LinearMap.ext fun f => ?_)
  let g : H.X.Ord (H.τA A) θ (H.lev K) :=
    ⟨((t : Module.End A (H.MK θ a K)) f : H.MK θ a K), ((t : Module.End A (H.MK θ a K)) f).2.1⟩
  have hg : g = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine hD _ fun x hx => ?_
    obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hAx A θ hθ ι x lam hx.2.1
    obtain ⟨h1, act, h2, -, -, -, h3⟩ := partAct0 hLit L Ω l n c H hAx A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
    have hE := h1.resolve_right (not_not.2 hx)
    have h0 := coreSep_kill _ _ hE (act t) (fun Y F hF => by
      by_cases hb : Y.1.Y ⊓ Submodule.span ℂ (sp '' H.MK θ a K) = ⊥
      · have : F = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hb _ ⟨hF, F.2⟩)
        rw [this, map_zero]
      · obtain ⟨y, hy, hact⟩ := h3 hx Y.1 hb
        rw [hact t F hF, ht y (hy ▸ hx), map_zero, zero_smul])
      ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩
    have h4 := h2 t f ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩ rfl
    rw [h0] at h4
    have h5 := coreSep_coord _ (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) b (hsp.indep K _ b) g h4.symm i
    exact ι.injective (h5.trans (map_zero ι).symm)
  exact Subtype.ext (congrArg (fun z : H.X.Ord (H.τA A) θ (H.lev K) => (z : H.X.Fn A H.m)) hg)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.FreeOfNeat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace UpperTheory.V.Hi.LvR

section Gen

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))

theorem c1 (i) : (rUp h).chib i = (r.chib i).comp (fh h).π₀ := rfl

theorem rUp_chib (i) (g : V.frame.G₀) : (rUp h).chib i g = r.chib i (p0 h g) := MonoidHom.comp_apply (r.chib i) (p0 h) g

theorem c2 (v i) : (rUp h).psib v i = (r.psib ((fh h).vl v) i).comp ((fh h).gv v) := MonoidHom.ext fun _ => rfl

theorem c3 (v i) (g : V.frame.mu v) (hg : (fh h).gv v g ∈ V0.frame.mu ((fh h).vl v)) : (rUp h).th v i g = r.th ((fh h).vl v) i ⟨_, hg⟩ := by
  have e : ∀ g : W.muG l (Dec (F := L) (s.A v.1)), (rUp h).th v i g = @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i) g := fun _ => rfl
  have e2 : ∀ (g : Dec (F := L) (s.A v.1)) (hg : g ∈ W.muG l (Dec (F := L) (s.A v.1))), @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i) ⟨g, hg⟩ = r.th v i ⟨g, hg⟩ := fun _ _ => rfl
  exact (e g).trans (e2 g.1 (@id (g.1 ∈ W.muG l (Dec (F := L) (s.A v.1))) g.2))

theorem c4 (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (u : s.St) (g : V.η.ker) (hg : g ∈ (rUp h).Ip u) : p0 h g ∈ r.Ip u := by
    obtain ⟨⟨x, hx, rfl⟩, h2⟩ := hg
    refine ⟨⟨x, hx, (levelChangeBaseGroupHom_apply_projection h hp x).symm⟩, ?_⟩
    exact Subgroup.mem_iInf.2 fun i => MonoidHom.mem_ker.2 ((rUp_chib h i _).symm.trans (MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 h2 i)))

theorem rUp_compat (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) : (fh h).Compat (rUp h) r :=
  ⟨c1 h, c2 h, c3 h, fun u g hg => Or.inr ⟨u, c4 h hp u g hg⟩⟩

theorem pairUp (hn : 1 ≤ n) (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair r R) :
    ∃ p' : Pair (rUp h) R, p'.D = p.D.comap (p0 h) ∧ ∀ (v : Vl l L) i, @Eq (Dec (F := L) (s.A v.1) →* Rˣ) (p'.ψ v i) (p.ψ v i) := by
  obtain ⟨p', h1, h2⟩ := W.exists_determinantPair_pullback l _ _ (fh h) O n (rUp h) r (rUp_compat h hp) (fun e => by omega) R p
  exact ⟨p', h1, fun v i => Eq.trans (h2 v i) rfl⟩

end Gen

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))

abbrev qUp (V : s.Lev) {q : ℕ} (w : Fin q → Plc L) (h1 : Function.Injective fun j => (w j).under (𝓞 (Lp L)))
    (h2 : ∀ j, (w j).under (𝓞 (Lp L)) ∉ s.S) (h3 : V.S' = s.S ∪ Set.range fun j => (w j).under (𝓞 (Lp L))) : QData V where
  Q := Fin q
  wq := w
  inj := h1
  notS := h2
  range := h3

variable (Q0 : QData V0) (Q : QData V) (hS : V0.S' ⊆ V.S')

def opUp {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : (hset Q τ₀).Op → (hset Q0 τ₀).Op
  | .inl x => .inl (⟨x.1.1, fun h => x.1.2.1 (hS h), x.1.2.2⟩, x.2)
  | .inr x => .inr x

def kMax {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : (hset Q τ₀).Lev :=
  ⟨fun _ => KO _ (Fin n), fun _ => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩

theorem free_of_neat {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (hU : X.Neat U) : X.Free τ θ U := by
  intro g γ u hu b hb e
  obtain ⟨rfl, rfl⟩ := hU g γ u hu b hb e
  refine ⟨one_mem _, one_mem _, ?_⟩
  have e1 : ∀ hh, (⟨1, hh⟩ : X.I.T) = 1 := fun _ => rfl
  rw [e1, map_one, map_one]
  simp

theorem teich_ext {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (x y : Oˣ) (h : residue O x = residue O y)
    (hx : x ^ (Nat.card (ResidueField O) - 1) = 1) (hy : y ^ (Nat.card (ResidueField O) - 1) = 1) : x = y := by
  set N := Nat.card (ResidueField O) - 1 with hN
  have hx' : (x : O) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hy' : (y : O) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]
  have e := (Commute.all (x : O) y).geom_sum₂_mul N
  rw [hx', hy', sub_self] at e
  have hu : IsUnit (∑ i ∈ Finset.range N, (x : O) ^ i * (y : O) ^ (N - 1 - i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← residue_ne_zero_iff_isUnit, map_sum]
    have : ∀ i ∈ Finset.range N, residue O ((x : O) ^ i * (y : O) ^ (N - 1 - i)) = residue O y ^ (N - 1) := fun i hi => by
      rw [map_mul, map_pow, map_pow, h, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine mul_ne_zero ?_ (pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).2 y.isUnit))
    haveI := Fintype.ofFinite (ResidueField O)
    rw [hN, Nat.cast_sub Nat.card_pos, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    simp
  exact Units.ext (sub_eq_zero.1 (hu.mul_right_eq_zero.1 e))

theorem typeFor_up (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ht : TypeFor r ι τ₀) : TypeFor (rUp h) ι τ₀ := by
  intro t' ht'
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  have hk : ∀ i, (p0 h).ker ≤ (t' i).ker := fun i g hg => by
    refine teich_ext _ _ ?_ (ht' i g).2 (one_pow _)
    rw [(ht' i g).1, rUp_chib, MonoidHom.mem_ker.1 hg, map_one]
    simp
  let t : Fin n → V0.frame.G₀ →* c.Oˣ := fun i => (p0 h).liftOfSurjective (surjective_levelChangeBaseGroupHom h) ⟨t' i, hk i⟩
  have e : ∀ i g, t i (p0 h g) = t' i g := fun i g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have := ht t fun i g => by
    obtain ⟨x, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    rw [e, ← rUp_chib]
    exact ht' i x
  have e2 : ∀ (u : s.St) i, (t' i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype) =
      (t i).comp (V0.pr.comp (Ine (F := L) (s.A u)).subtype) := fun u i => MonoidHom.ext fun x =>
    (e i (V.pr x)).symm.trans (congrArg (t i) (levelChangeBaseGroupHom_apply_projection h hp x))
  simp only [e2]
  exact this

theorem cont_up {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) {A : Type} [CommRing A] [IsLocalRing A]
    (θ : (hset Q0 τ₀).X.I.T →* Aˣ) (hθ : (hset Q0 τ₀).X.I.ContChar θ) : (hset Q τ₀).X.I.ContChar θ := hθ

theorem res_up (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (a : (hset Q0 τ₀).Op → c.O) (ha : IsRes Q0 r τ₀ a) : IsRes Q (rUp h) τ₀ fun i => a (opUp Q0 Q hS τ₀ i) := by
  refine ⟨fun w B σ hB hσ => ?_, ?_⟩
  · refine (congrArg (fun D : W.GDet n (ResidueField c.O) V.frame.G₀ => D.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1))
      (rUp_Dbar h)).trans ((chi_comap r.Dbar (p0 h) (V.pr σ⁻¹)).trans ?_)
    exact (congrArg (fun g : V0.frame.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1)) (levelChangeBaseGroupHom_apply_projection h hp σ⁻¹)).trans
      (ha.frob ⟨w.1, fun h => w.2.1 (hS h), w.2.2⟩ B σ hB hσ)
  · have := ha.unif
    cases r
    exact this


end UpperTheory.V.Hi.LvR
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LNotMemBasePrime
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem l_not_mem_base_prime {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have h1 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← s.norm_v0_eq_one]
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      Ideal.absNorm_mem s.v0.asIdeal
  have hc : IsCoprime (s.p : 𝓞 (Lp L)) (l : 𝓞 (Lp L)) :=
    ((Nat.coprime_primes s.p_prime Fact.out).2 s.p_ne).cast
  obtain ⟨a, b, hab⟩ := hc
  exact s.v0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h)))

private theorem sum_one {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ} {H : Type} [Group H] (τ : H →* GL (Fin m) ℂ)
    (f : Fin m → M) (i : Fin m) : ∑ j : Fin m, τ 1 i j • f j = f i := by
  simp [Matrix.one_apply]

theorem UpperTheory.V.Hi.partUR2V0 :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ → fixd τ.ρ (Kc _ n 1) ≠ ⊥ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hY τ hτ
  have hw0 := w_under s s.v0
  have hsp : IsSplitAt (s.w s.v0) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA s.v0) (s.split _ (Or.inr (Or.inr rfl))) _ hw0
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (UpperTheory.V.Hi.secU l L Ω s n hn _ hsp).1
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ j hj1 hj2 hj3 τ hτ
  obtain ⟨h1, -, -, h4⟩ := UpperTheory.V.Hi.partUR2Abs L n _ _ _ _ τ hiso
  refine h1 _ (h4 1) ?_
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hM⟩ := (UpperTheory.V.Hi.partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have hinj := (UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  intro hbot
  refine hF0 (funext fun i => hinj (F i) (And.left hB i (Set.mem_univ i)) fun ℓ => ?_)
  refine (Submodule.eq_bot_iff _).1 hbot _ (Submodule.mem_inf.2 ⟨hM i ℓ, fun g hg => ?_⟩)
  have hloc : ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ s.v0 → cLoc u (j g) = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (hj1 g)).2 u) (hw0.symm ▸ hu))
  have h := UpperTheory.V.Hi.partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ F hB (j g) (Subgroup.mem_inf.1 (hj1 g)).1
    (fun v => hloc _ fun h => l_not_mem_base_prime s (by
      rw [← h, w_under]
      exact v.2)) 1
    (fun u => (hloc _ fun h => s.v0_St (by
      rw [← h, w_under]
      exact u.2)).symm)
    ((hj2 g).symm ▸ hg)
    (fun w hw => by
      rw [hloc w fun h => hw (V.sub (Or.inr (Or.inr h)))]
      exact one_mem _)
    (fun q => hloc _ fun h => Q.notS q (Or.inr (Or.inr h))) i ℓ
  exact (sum_one _ (fun j' => RU L n (j g) (toForm ι e (F j') ℓ)) i).symm.trans h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Faith
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2Faith :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) [DecidableEq Q.Q] (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (k : GV n Q.wq) (j : GV n Q.wq →* Ub n s), (∀ q g, j (Pi.mulSingle q g) = sec n s (Q.wq q) g) → j k ∈ (hset Q τ₀).lev K → k ∈ Subgroup.pi Set.univ K.1 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q _ c m τ₀ K k j hj hk
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  have key : ∀ q : Q.Q, ((CaseU.cmp n (Q.wq q)).comp (Ub n s).subtype).comp j =
      Pi.evalMonoidHom (fun q : Q.Q => GLw n (Q.wq q)) q := fun q => by
    refine MonoidHom.pi_ext fun q' g => ?_
    change CaseU.cmp n (Q.wq q) ((j (Pi.mulSingle q' g) : Ub n s) : Ga l L n) =
      (Pi.mulSingle q' g : ∀ q : Q.Q, GLw n (Q.wq q)) q
    rw [hj]
    by_cases h : q = q'
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact (hsec q).2.1 g
    · rw [Pi.mulSingle_eq_of_ne h]
      exact h1 q' g _ fun h' => h (Q.inj h')
  intro q _
  have h2 := (levelUR2LevOut l L Ω s n hn V Q c m τ₀ K (j k) hk).2 q
  have h3 : CaseU.cmp n (Q.wq q) ((j k : Ub n s) : Ga l L n) = k q := DFunLike.congr_fun (key q) k
  rw [h3] at h2
  exact h2
end

